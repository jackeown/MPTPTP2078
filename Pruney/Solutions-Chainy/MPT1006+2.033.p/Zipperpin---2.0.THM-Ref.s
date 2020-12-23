%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vhM0kia1Ff

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:11 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  84 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 569 expanded)
%              Number of equality atoms :   30 (  64 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C_1 @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('18',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','14'])).

thf('19',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vhM0kia1Ff
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:57:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.47  % Solved by: fo/fo7.sh
% 0.18/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.47  % done 42 iterations in 0.021s
% 0.18/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.47  % SZS output start Refutation
% 0.18/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.18/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.18/0.47  thf(t60_funct_2, conjecture,
% 0.18/0.47    (![A:$i,B:$i,C:$i]:
% 0.18/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.18/0.47         ( m1_subset_1 @
% 0.18/0.47           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.18/0.47       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.18/0.47            ( m1_subset_1 @
% 0.18/0.47              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.18/0.47          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.18/0.47    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.18/0.47  thf('0', plain,
% 0.18/0.47      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C_1 @ sk_B) != (k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf('1', plain,
% 0.18/0.47      ((m1_subset_1 @ sk_C_1 @ 
% 0.18/0.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.18/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.47  thf(t113_zfmisc_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.47  thf('2', plain,
% 0.18/0.47      (![X7 : $i, X8 : $i]:
% 0.18/0.47         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.18/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.18/0.47  thf('3', plain,
% 0.18/0.47      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.18/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.18/0.47  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['1', '3'])).
% 0.18/0.47  thf(d2_subset_1, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.18/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.18/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.18/0.47  thf('5', plain,
% 0.18/0.47      (![X9 : $i, X10 : $i]:
% 0.18/0.47         (~ (m1_subset_1 @ X9 @ X10)
% 0.18/0.47          | (r2_hidden @ X9 @ X10)
% 0.18/0.47          | (v1_xboole_0 @ X10))),
% 0.18/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.18/0.47  thf('6', plain,
% 0.18/0.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.18/0.47        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.18/0.47  thf(t1_zfmisc_1, axiom,
% 0.18/0.47    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.18/0.47  thf('7', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.18/0.47  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.18/0.47  thf('8', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.18/0.47      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.18/0.47  thf('9', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.47  thf('10', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.18/0.47      inference('clc', [status(thm)], ['6', '9'])).
% 0.18/0.47  thf('11', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.18/0.47  thf(d1_tarski, axiom,
% 0.18/0.47    (![A:$i,B:$i]:
% 0.18/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.18/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.18/0.47  thf('12', plain,
% 0.18/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.18/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.47  thf('13', plain,
% 0.18/0.47      (![X0 : $i, X3 : $i]:
% 0.18/0.47         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.18/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.18/0.47  thf('14', plain,
% 0.18/0.47      (![X0 : $i]:
% 0.18/0.47         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.18/0.47          | ((X0) = (k1_xboole_0)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['11', '13'])).
% 0.18/0.47  thf('15', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['10', '14'])).
% 0.18/0.47  thf('16', plain,
% 0.18/0.47      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B)
% 0.18/0.47         != (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['0', '15'])).
% 0.18/0.47  thf('17', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['1', '3'])).
% 0.18/0.47  thf('18', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['10', '14'])).
% 0.18/0.47  thf('19', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.18/0.47  thf('20', plain,
% 0.18/0.47      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.18/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.18/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.18/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.18/0.47  thf('21', plain,
% 0.18/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.18/0.47          | ((k8_relset_1 @ X14 @ X15 @ X13 @ X16) = (k10_relat_1 @ X13 @ X16)))),
% 0.18/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.18/0.47  thf('22', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.18/0.47          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.18/0.47              = (k10_relat_1 @ X1 @ X2)))),
% 0.18/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.18/0.47  thf('23', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0)
% 0.18/0.47           = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.18/0.47      inference('sup-', [status(thm)], ['19', '22'])).
% 0.18/0.47  thf(t172_relat_1, axiom,
% 0.18/0.47    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.18/0.47  thf('24', plain,
% 0.18/0.47      (![X12 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.18/0.47      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.18/0.47  thf('25', plain,
% 0.18/0.47      (![X0 : $i, X1 : $i]:
% 0.18/0.47         ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.18/0.47  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.47      inference('demod', [status(thm)], ['16', '25'])).
% 0.18/0.47  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.18/0.47  
% 0.18/0.47  % SZS output end Refutation
% 0.18/0.47  
% 0.18/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
