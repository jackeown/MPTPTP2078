%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZcitjBJLwO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  432 ( 935 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['4','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( ( k8_relset_1 @ X19 @ X21 @ X20 @ X21 )
        = X19 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ k1_xboole_0 @ X21 @ X20 @ X21 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ k1_xboole_0 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ k1_xboole_0 @ X21 @ X20 @ X21 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ X20 @ k1_xboole_0 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k10_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( v1_funct_2 @ X22 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['31','32','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','38'])).

thf('40',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZcitjBJLwO
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 152 iterations in 0.081s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(t60_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.53       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.21/0.53            ( m1_subset_1 @
% 0.21/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.21/0.53          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t113_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('4', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf(cc3_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 0.21/0.54          | (v1_xboole_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | (v1_xboole_0 @ X1)
% 0.21/0.54          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.54  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain, ((v1_xboole_0 @ sk_C)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.54  thf(l13_xboole_0, axiom,
% 0.21/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.54  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.21/0.54         != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '12'])).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.54          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.21/0.54           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('17', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(t48_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.54         (((X19) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_funct_1 @ X20)
% 0.21/0.54          | ~ (v1_funct_2 @ X20 @ X19 @ X21)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 0.21/0.54          | ((k8_relset_1 @ X19 @ X21 @ X20 @ X21) = (X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (((k8_relset_1 @ k1_xboole_0 @ X21 @ X20 @ X21) = (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.54               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X21)))
% 0.21/0.54          | ~ (v1_funct_2 @ X20 @ k1_xboole_0 @ X21)
% 0.21/0.54          | ~ (v1_funct_1 @ X20))),
% 0.21/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (((k8_relset_1 @ k1_xboole_0 @ X21 @ X20 @ X21) = (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.21/0.54          | ~ (v1_funct_2 @ X20 @ k1_xboole_0 @ X21)
% 0.21/0.54          | ~ (v1_funct_1 @ X20))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ X0)
% 0.21/0.54              = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.54  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('26', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((k8_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.21/0.54           = (k10_relat_1 @ k1_xboole_0 @ X2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.54          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.21/0.54  thf(t60_relat_1, axiom,
% 0.21/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('29', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf(t4_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.54         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.54           ( m1_subset_1 @
% 0.21/0.54             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.21/0.54          | (v1_funct_2 @ X22 @ (k1_relat_1 @ X22) @ X23)
% 0.21/0.54          | ~ (v1_funct_1 @ X22)
% 0.21/0.54          | ~ (v1_relat_1 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.54          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('32', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X9)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('38', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '32', '35', '36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '38'])).
% 0.21/0.54  thf('40', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '39'])).
% 0.21/0.54  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
