%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UdIzSrGhiU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:00 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 214 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  643 (2842 expanded)
%              Number of equality atoms :   40 ( 151 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ( X56
        = ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ~ ( zip_tseitin_1 @ X58 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X60 )
      | ( zip_tseitin_1 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relset_1 @ X44 @ X45 @ X43 )
        = ( k1_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X35 )
       != ( k1_tarski @ X34 ) )
      | ( ( k2_relat_1 @ X35 )
        = ( k1_tarski @ ( k1_funct_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X50 ) @ X51 )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('43',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k7_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k9_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['31','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UdIzSrGhiU
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 141 iterations in 0.292s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.55/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.55/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.74  thf(t64_funct_2, conjecture,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.55/0.74         ( m1_subset_1 @
% 0.55/0.74           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.55/0.74       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.55/0.74         ( r1_tarski @
% 0.55/0.74           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.55/0.74           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.55/0.74            ( m1_subset_1 @
% 0.55/0.74              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.55/0.74          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.55/0.74            ( r1_tarski @
% 0.55/0.74              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.55/0.74              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (~ (r1_tarski @ 
% 0.55/0.74          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.55/0.74          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d1_funct_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.55/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.55/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.55/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_1, axiom,
% 0.55/0.74    (![C:$i,B:$i,A:$i]:
% 0.55/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.55/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.55/0.74         (~ (v1_funct_2 @ X58 @ X56 @ X57)
% 0.55/0.74          | ((X56) = (k1_relset_1 @ X56 @ X57 @ X58))
% 0.55/0.74          | ~ (zip_tseitin_1 @ X58 @ X57 @ X56))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.55/0.74        | ((k1_tarski @ sk_A)
% 0.55/0.74            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf(zf_stmt_2, axiom,
% 0.55/0.74    (![B:$i,A:$i]:
% 0.55/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.55/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X54 : $i, X55 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_5, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.55/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.55/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.55/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.55/0.74         (~ (zip_tseitin_0 @ X59 @ X60)
% 0.55/0.74          | (zip_tseitin_1 @ X61 @ X59 @ X60)
% 0.55/0.74          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.55/0.74        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      ((((sk_B) = (k1_xboole_0))
% 0.55/0.74        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['4', '7'])).
% 0.55/0.74  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.55/0.74         (((k1_relset_1 @ X44 @ X45 @ X43) = (k1_relat_1 @ X43))
% 0.55/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.55/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (~ (r1_tarski @ 
% 0.55/0.74          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.55/0.74          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['0', '14'])).
% 0.55/0.74  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.55/0.74  thf(t14_funct_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.74       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.55/0.74         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X34 : $i, X35 : $i]:
% 0.55/0.74         (((k1_relat_1 @ X35) != (k1_tarski @ X34))
% 0.55/0.74          | ((k2_relat_1 @ X35) = (k1_tarski @ (k1_funct_1 @ X35 @ X34)))
% 0.55/0.74          | ~ (v1_funct_1 @ X35)
% 0.55/0.74          | ~ (v1_relat_1 @ X35))),
% 0.55/0.74      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.55/0.74        | ~ (v1_funct_1 @ sk_D)
% 0.55/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.55/0.74      inference('eq_res', [status(thm)], ['18'])).
% 0.55/0.74  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(cc1_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( v1_relat_1 @ C ) ))).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.55/0.74         ((v1_relat_1 @ X36)
% 0.55/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.74  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (~ (r1_tarski @ 
% 0.55/0.74          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.55/0.74          (k2_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['15', '24'])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('27', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.55/0.74          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.55/0.74           = (k9_relat_1 @ sk_D @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['25', '30'])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.74      inference('simplify', [status(thm)], ['32'])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf(t14_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.55/0.74       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.55/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X50) @ X51)
% 0.55/0.74          | (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.55/0.74          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.55/0.74      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_subset_1 @ sk_D @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.55/0.74          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['33', '36'])).
% 0.55/0.74  thf(dt_k7_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.55/0.74          | (m1_subset_1 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X42) @ 
% 0.55/0.74             (k1_zfmisc_1 @ X41)))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (m1_subset_1 @ 
% 0.55/0.74          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 0.55/0.74          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf(t3_subset, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X31 : $i, X32 : $i]:
% 0.55/0.74         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (r1_tarski @ 
% 0.55/0.74          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 0.55/0.74          (k2_relat_1 @ sk_D))),
% 0.55/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_D @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['33', '36'])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.55/0.74          | ((k7_relset_1 @ X47 @ X48 @ X46 @ X49) = (k9_relat_1 @ X46 @ X49)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0)
% 0.55/0.74           = (k9_relat_1 @ sk_D @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['41', '44'])).
% 0.55/0.74  thf('46', plain, ($false), inference('demod', [status(thm)], ['31', '45'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
