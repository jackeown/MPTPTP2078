%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GoeZnyZkX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:03 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  57 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  256 ( 298 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t59_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_2])).

thf('0',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k7_relset_1 @ X18 @ X19 @ X17 @ X20 )
        = ( k9_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','22'])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['8','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GoeZnyZkX
% 0.15/0.37  % Computer   : n002.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 121 iterations in 0.065s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.55  thf(t59_funct_2, conjecture,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.24/0.55         ( m1_subset_1 @
% 0.24/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.24/0.55       ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.24/0.55            ( m1_subset_1 @
% 0.24/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.24/0.55          ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t59_funct_2])).
% 0.24/0.55  thf('0', plain,
% 0.24/0.55      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('1', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(cc3_relset_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.24/0.55       ( ![C:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.55           ( v1_xboole_0 @ C ) ) ) ))).
% 0.24/0.55  thf('2', plain,
% 0.24/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.55         (~ (v1_xboole_0 @ X14)
% 0.24/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 0.24/0.55          | (v1_xboole_0 @ X15))),
% 0.24/0.55      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.24/0.55  thf('3', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.55  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.55  thf('5', plain, ((v1_xboole_0 @ sk_C)),
% 0.24/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.55  thf(l13_xboole_0, axiom,
% 0.24/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.55  thf('6', plain,
% 0.24/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.24/0.55  thf('7', plain, (((sk_C) = (k1_xboole_0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.24/0.55         != (k1_xboole_0))),
% 0.24/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.24/0.55  thf(t4_subset_1, axiom,
% 0.24/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.24/0.55  thf('10', plain,
% 0.24/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.24/0.55          | ((k7_relset_1 @ X18 @ X19 @ X17 @ X20) = (k9_relat_1 @ X17 @ X20)))),
% 0.24/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.24/0.55           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.24/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.55  thf(t60_relat_1, axiom,
% 0.24/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.55  thf('12', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.55  thf(t144_relat_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( v1_relat_1 @ B ) =>
% 0.24/0.55       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.24/0.55  thf('13', plain,
% 0.24/0.55      (![X9 : $i, X10 : $i]:
% 0.24/0.55         ((r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k2_relat_1 @ X9))
% 0.24/0.55          | ~ (v1_relat_1 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.24/0.55          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.24/0.55  thf(cc1_relset_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.55       ( v1_relat_1 @ C ) ))).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.24/0.55         ((v1_relat_1 @ X11)
% 0.24/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.24/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.55  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.24/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.24/0.55      inference('demod', [status(thm)], ['14', '17'])).
% 0.24/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.55  thf('19', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.24/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.55  thf(d10_xboole_0, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.55  thf('20', plain,
% 0.24/0.55      (![X1 : $i, X3 : $i]:
% 0.24/0.55         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.24/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.55  thf('22', plain,
% 0.24/0.55      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['18', '21'])).
% 0.24/0.55  thf('23', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.24/0.55      inference('demod', [status(thm)], ['11', '22'])).
% 0.24/0.55  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.24/0.55      inference('demod', [status(thm)], ['8', '23'])).
% 0.24/0.55  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
