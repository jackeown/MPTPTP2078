%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cwFwA5KMP6

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:21 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 183 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  685 (1910 expanded)
%              Number of equality atoms :   47 (  93 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ X40 @ ( k1_relat_1 @ X41 ) )
      | ( X42 = k1_xboole_0 )
      | ( X42
       != ( k1_funct_1 @ X41 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k1_funct_1 @ X41 @ X40 )
        = k1_xboole_0 )
      | ( r2_hidden @ X40 @ ( k1_relat_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X45 @ X44 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v5_relat_1 @ X51 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v5_relat_1 @ X38 @ X39 )
      | ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X39 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v1_relat_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['10','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['10','13'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('28',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ( X59
        = ( k1_relset_1 @ X59 @ X60 @ X61 ) )
      | ~ ( zip_tseitin_1 @ X61 @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X57 @ X58 )
      | ( X57 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('32',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( zip_tseitin_0 @ X62 @ X63 )
      | ( zip_tseitin_1 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( ( k1_relset_1 @ X55 @ X56 @ X54 )
        = ( k1_relat_1 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','36','39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ X47 )
       != ( k1_tarski @ X46 ) )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_tarski @ ( k1_funct_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ sk_B ),
    inference(demod,[status(thm)],['26','48'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['25','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cwFwA5KMP6
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 173 iterations in 0.160s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(t61_funct_2, conjecture,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.62         ( m1_subset_1 @
% 0.38/0.62           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.62            ( m1_subset_1 @
% 0.38/0.62              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.38/0.62  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d4_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ![B:$i,C:$i]:
% 0.38/0.62         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.62             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.62               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.62           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.38/0.62             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.38/0.62               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.62         ((r2_hidden @ X40 @ (k1_relat_1 @ X41))
% 0.38/0.62          | ((X42) = (k1_xboole_0))
% 0.38/0.62          | ((X42) != (k1_funct_1 @ X41 @ X40))
% 0.38/0.62          | ~ (v1_funct_1 @ X41)
% 0.38/0.62          | ~ (v1_relat_1 @ X41))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X40 : $i, X41 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X41)
% 0.38/0.62          | ~ (v1_funct_1 @ X41)
% 0.38/0.62          | ((k1_funct_1 @ X41 @ X40) = (k1_xboole_0))
% 0.38/0.62          | (r2_hidden @ X40 @ (k1_relat_1 @ X41)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.62  thf(t12_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.62         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X44 : $i, X45 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X44 @ (k1_relat_1 @ X45))
% 0.38/0.62          | (r2_hidden @ (k1_funct_1 @ X45 @ X44) @ (k2_relat_1 @ X45))
% 0.38/0.62          | ~ (v1_funct_1 @ X45)
% 0.38/0.62          | ~ (v1_relat_1 @ X45))),
% 0.38/0.62      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc2_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.38/0.62         ((v5_relat_1 @ X51 @ X53)
% 0.38/0.62          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('8', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf(d19_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X38 : $i, X39 : $i]:
% 0.38/0.62         (~ (v5_relat_1 @ X38 @ X39)
% 0.38/0.62          | (r1_tarski @ (k2_relat_1 @ X38) @ X39)
% 0.38/0.62          | ~ (v1_relat_1 @ X38))),
% 0.38/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc1_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( v1_relat_1 @ C ) ))).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.38/0.62         ((v1_relat_1 @ X48)
% 0.38/0.62          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.62  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X35 : $i, X37 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf(l3_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X32 @ X33)
% 0.38/0.62          | (r2_hidden @ X32 @ X34)
% 0.38/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.38/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['5', '18'])).
% 0.38/0.62  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_funct_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.38/0.62          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.62  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('24', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['0', '24'])).
% 0.38/0.62  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['10', '13'])).
% 0.38/0.62  thf('27', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d1_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, axiom,
% 0.38/0.62    (![C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.38/0.62         (~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.38/0.62          | ((X59) = (k1_relset_1 @ X59 @ X60 @ X61))
% 0.38/0.62          | ~ (zip_tseitin_1 @ X61 @ X60 @ X59))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.62        | ((k1_tarski @ sk_A)
% 0.38/0.62            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf(zf_stmt_2, axiom,
% 0.38/0.62    (![B:$i,A:$i]:
% 0.38/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X57 : $i, X58 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X57 @ X58) | ((X57) = (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_5, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.38/0.62         (~ (zip_tseitin_0 @ X62 @ X63)
% 0.38/0.62          | (zip_tseitin_1 @ X64 @ X62 @ X63)
% 0.38/0.62          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.62        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      ((((sk_B) = (k1_xboole_0))
% 0.38/0.62        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['30', '33'])).
% 0.38/0.62  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('36', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.38/0.62         (((k1_relset_1 @ X55 @ X56 @ X54) = (k1_relat_1 @ X54))
% 0.38/0.62          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 0.38/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.62  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.62      inference('demod', [status(thm)], ['29', '36', '39'])).
% 0.38/0.62  thf(t14_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.38/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X46 : $i, X47 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X47) != (k1_tarski @ X46))
% 0.38/0.62          | ((k2_relat_1 @ X47) = (k1_tarski @ (k1_funct_1 @ X47 @ X46)))
% 0.38/0.62          | ~ (v1_funct_1 @ X47)
% 0.38/0.62          | ~ (v1_relat_1 @ X47))),
% 0.38/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.62  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_tarski @ sk_A) != (k1_tarski @ X0))
% 0.38/0.62          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.38/0.62      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.38/0.62      inference('eq_res', [status(thm)], ['45'])).
% 0.38/0.62  thf('47', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('48', plain, (((k2_relat_1 @ sk_C) = (k1_tarski @ k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.62  thf('49', plain, ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ sk_B)),
% 0.38/0.62      inference('demod', [status(thm)], ['26', '48'])).
% 0.38/0.62  thf(t69_enumset1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.62  thf('50', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.62  thf(t38_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         ((r2_hidden @ X28 @ X29)
% 0.38/0.62          | ~ (r1_tarski @ (k2_tarski @ X28 @ X30) @ X29))),
% 0.38/0.62      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.62  thf('53', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.38/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.38/0.62  thf('54', plain, ($false), inference('demod', [status(thm)], ['25', '53'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
