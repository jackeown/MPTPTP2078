%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StvuA5Aa8b

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:10 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 217 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  658 (2857 expanded)
%              Number of equality atoms :   40 ( 151 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( v1_funct_2 @ X59 @ X57 @ X58 )
      | ( X57
        = ( k1_relset_1 @ X57 @ X58 @ X59 ) )
      | ~ ( zip_tseitin_1 @ X59 @ X58 @ X57 ) ) ),
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
    ! [X55: $i,X56: $i] :
      ( ( zip_tseitin_0 @ X55 @ X56 )
      | ( X55 = k1_xboole_0 ) ) ),
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
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( zip_tseitin_0 @ X60 @ X61 )
      | ( zip_tseitin_1 @ X62 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X60 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X46 @ X44 )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ X39 )
       != ( k1_tarski @ X38 ) )
      | ( ( k2_relat_1 @ X39 )
        = ( k1_tarski @ ( k1_funct_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X51 ) @ X52 )
      | ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('45',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['33','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.StvuA5Aa8b
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 141 iterations in 0.213s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(t64_funct_2, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.67         ( m1_subset_1 @
% 0.47/0.67           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.67       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.67         ( r1_tarski @
% 0.47/0.67           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.67           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.47/0.67            ( m1_subset_1 @
% 0.47/0.67              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.47/0.67          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.47/0.67            ( r1_tarski @
% 0.47/0.67              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.47/0.67              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d1_funct_2, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_1, axiom,
% 0.47/0.67    (![C:$i,B:$i,A:$i]:
% 0.47/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.47/0.67         (~ (v1_funct_2 @ X59 @ X57 @ X58)
% 0.47/0.67          | ((X57) = (k1_relset_1 @ X57 @ X58 @ X59))
% 0.47/0.67          | ~ (zip_tseitin_1 @ X59 @ X58 @ X57))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.67        | ((k1_tarski @ sk_A)
% 0.47/0.67            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.67  thf(zf_stmt_2, axiom,
% 0.47/0.67    (![B:$i,A:$i]:
% 0.47/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X55 : $i, X56 : $i]:
% 0.47/0.67         ((zip_tseitin_0 @ X55 @ X56) | ((X55) = (k1_xboole_0)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.67  thf(zf_stmt_5, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.47/0.67         (~ (zip_tseitin_0 @ X60 @ X61)
% 0.47/0.67          | (zip_tseitin_1 @ X62 @ X60 @ X61)
% 0.47/0.67          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X60))))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.47/0.67        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      ((((sk_B) = (k1_xboole_0))
% 0.47/0.67        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['4', '7'])).
% 0.47/0.67  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.47/0.67         (((k1_relset_1 @ X45 @ X46 @ X44) = (k1_relat_1 @ X44))
% 0.47/0.67          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['0', '14'])).
% 0.47/0.67  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.47/0.67  thf(t14_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.67         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X38 : $i, X39 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X39) != (k1_tarski @ X38))
% 0.47/0.67          | ((k2_relat_1 @ X39) = (k1_tarski @ (k1_funct_1 @ X39 @ X38)))
% 0.47/0.67          | ~ (v1_funct_1 @ X39)
% 0.47/0.67          | ~ (v1_relat_1 @ X39))),
% 0.47/0.67      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_funct_1 @ X0)
% 0.47/0.67          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.47/0.67        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('eq_res', [status(thm)], ['18'])).
% 0.47/0.67  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(cc2_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X34 : $i, X35 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.47/0.67          | (v1_relat_1 @ X34)
% 0.47/0.67          | ~ (v1_relat_1 @ X35))),
% 0.47/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.47/0.67        | (v1_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.67  thf(fc6_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X36 : $i, X37 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X36 @ X37))),
% 0.47/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.67  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.67      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['19', '20', '25'])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (~ (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.47/0.67          (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['15', '26'])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf(redefinition_k7_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.47/0.67          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.47/0.67           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['27', '32'])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf(t14_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.47/0.67       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.47/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.47/0.67         (~ (r1_tarski @ (k2_relat_1 @ X51) @ X52)
% 0.47/0.67          | (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.47/0.67          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.47/0.67      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((m1_subset_1 @ sk_D @ 
% 0.47/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.47/0.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['35', '38'])).
% 0.47/0.67  thf(dt_k7_relset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.67       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.47/0.67          | (m1_subset_1 @ (k7_relset_1 @ X41 @ X42 @ X40 @ X43) @ 
% 0.47/0.67             (k1_zfmisc_1 @ X42)))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (m1_subset_1 @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 0.47/0.67          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.67  thf(t3_subset, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X31 : $i, X32 : $i]:
% 0.47/0.67         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (r1_tarski @ 
% 0.47/0.67          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 0.47/0.67          (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      ((m1_subset_1 @ sk_D @ 
% 0.47/0.67        (k1_zfmisc_1 @ 
% 0.47/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['35', '38'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.47/0.67         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.47/0.67          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 0.47/0.67      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0)
% 0.47/0.67           = (k9_relat_1 @ sk_D @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('47', plain,
% 0.47/0.67      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.47/0.67      inference('demod', [status(thm)], ['43', '46'])).
% 0.47/0.67  thf('48', plain, ($false), inference('demod', [status(thm)], ['33', '47'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
