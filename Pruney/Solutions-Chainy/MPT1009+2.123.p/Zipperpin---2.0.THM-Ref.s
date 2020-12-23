%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYM6MmCMfh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:06 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 205 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  562 (2169 expanded)
%              Number of equality atoms :   40 ( 109 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k7_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k9_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X59 ) @ X60 )
      | ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X61 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X47 @ X48 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v4_relat_1 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v4_relat_1 @ X43 @ X44 )
      | ( r1_tarski @ ( k1_relat_1 @ X43 ) @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_relat_1 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X45: $i,X46: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ X51 )
       != ( k1_tarski @ X50 ) )
      | ( ( k2_relat_1 @ X51 )
        = ( k1_tarski @ ( k1_funct_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['18','19'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X49: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X49 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('47',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('48',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['4','45','46','47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VYM6MmCMfh
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 156 iterations in 0.077s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(t64_funct_2, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.53         ( m1_subset_1 @
% 0.35/0.53           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53         ( r1_tarski @
% 0.35/0.53           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.35/0.53           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.53            ( m1_subset_1 @
% 0.35/0.53              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53            ( r1_tarski @
% 0.35/0.53              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.35/0.53              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (~ (r1_tarski @ 
% 0.35/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.35/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_D @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.35/0.53          | ((k7_relset_1 @ X56 @ X57 @ X55 @ X58) = (k9_relat_1 @ X55 @ X58)))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.35/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.35/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.35/0.53  thf(t113_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X36 : $i, X37 : $i]:
% 0.35/0.53         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 0.35/0.53          | ((X36) != (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_D @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t13_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.35/0.53       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.35/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_relat_1 @ X59) @ X60)
% 0.35/0.53          | (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.35/0.53          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X61))))),
% 0.35/0.53      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.35/0.53          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf(t144_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X47 : $i, X48 : $i]:
% 0.35/0.53         ((r1_tarski @ (k9_relat_1 @ X47 @ X48) @ (k2_relat_1 @ X47))
% 0.35/0.53          | ~ (v1_relat_1 @ X47))),
% 0.35/0.53      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_D @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.35/0.53         ((v4_relat_1 @ X52 @ X53)
% 0.35/0.53          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.53  thf('13', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf(d18_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X43 : $i, X44 : $i]:
% 0.35/0.53         (~ (v4_relat_1 @ X43 @ X44)
% 0.35/0.53          | (r1_tarski @ (k1_relat_1 @ X43) @ X44)
% 0.35/0.53          | ~ (v1_relat_1 @ X43))),
% 0.35/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.35/0.53        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_D @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X41 : $i, X42 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.35/0.53          | (v1_relat_1 @ X41)
% 0.35/0.53          | ~ (v1_relat_1 @ X42))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.35/0.53        | (v1_relat_1 @ sk_D))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf(fc6_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X45 : $i, X46 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X45 @ X46))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.53  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '20'])).
% 0.35/0.53  thf(l3_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.35/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X32 : $i, X33 : $i]:
% 0.35/0.53         (((X33) = (k1_tarski @ X32))
% 0.35/0.53          | ((X33) = (k1_xboole_0))
% 0.35/0.53          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.35/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.35/0.53        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.53  thf(t14_funct_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.35/0.53         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X50 : $i, X51 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X51) != (k1_tarski @ X50))
% 0.35/0.53          | ((k2_relat_1 @ X51) = (k1_tarski @ (k1_funct_1 @ X51 @ X50)))
% 0.35/0.53          | ~ (v1_funct_1 @ X51)
% 0.35/0.53          | ~ (v1_relat_1 @ X51))),
% 0.35/0.53      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.35/0.53          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.35/0.53        | ~ (v1_funct_1 @ sk_D)
% 0.35/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.35/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.35/0.53      inference('eq_res', [status(thm)], ['25'])).
% 0.35/0.53  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.35/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (~ (r1_tarski @ 
% 0.35/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.35/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      ((~ (r1_tarski @ 
% 0.35/0.53           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.35/0.53           (k2_relat_1 @ sk_D))
% 0.35/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.35/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.35/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '33'])).
% 0.35/0.53  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf('36', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.53  thf('37', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['9', '36', '37'])).
% 0.35/0.53  thf('39', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['6', '38'])).
% 0.35/0.53  thf(t3_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X38 : $i, X39 : $i]:
% 0.35/0.53         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.53  thf('41', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf('42', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf(d10_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X0 : $i, X2 : $i]:
% 0.35/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('45', plain, (((sk_D) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['41', '44'])).
% 0.35/0.53  thf(t150_relat_1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X49 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X49) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.35/0.53  thf('47', plain, (((sk_D) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['41', '44'])).
% 0.35/0.53  thf('48', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf('49', plain, ($false),
% 0.35/0.53      inference('demod', [status(thm)], ['4', '45', '46', '47', '48'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
