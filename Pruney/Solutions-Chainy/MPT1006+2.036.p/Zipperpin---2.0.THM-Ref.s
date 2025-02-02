%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NcSPvaA48G

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 ( 737 expanded)
%              Number of equality atoms :   32 (  95 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 @ X12 )
      = ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X6 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 @ X12 )
      = ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k4_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( X5 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X6 @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X1 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','13','16'])).

thf(t47_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ X13 @ X14 @ X15 @ X16 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NcSPvaA48G
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 61 iterations in 0.025s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(t60_funct_2, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.19/0.47         ( m1_subset_1 @
% 0.19/0.47           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.19/0.47       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.19/0.47            ( m1_subset_1 @
% 0.19/0.47              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.19/0.47          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t54_mcart_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.19/0.47       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11 @ X12)
% 0.19/0.47           = (k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.19/0.47  thf(t35_mcart_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.19/0.47       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.47         (((X8) != (k1_xboole_0))
% 0.19/0.47          | ((k3_zfmisc_1 @ X5 @ X6 @ X8) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ X5 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.47  thf(d4_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.19/0.47       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         ((k4_zfmisc_1 @ X1 @ X2 @ X3 @ X4)
% 0.19/0.47           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ X2 @ X3) @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.19/0.47           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['5', '8'])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11 @ X12)
% 0.19/0.47           = (k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 0.19/0.47           = (k4_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.47         (((X5) != (k1_xboole_0))
% 0.19/0.47          | ((k3_zfmisc_1 @ X5 @ X6 @ X8) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X6 : $i, X8 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X6 : $i, X8 : $i]:
% 0.19/0.47         ((k3_zfmisc_1 @ k1_xboole_0 @ X6 @ X8) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         ((k4_zfmisc_1 @ X1 @ X2 @ X3 @ X4)
% 0.19/0.47           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X1 @ X2 @ X3) @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         ((k4_zfmisc_1 @ k1_xboole_0 @ X2 @ X1 @ X0)
% 0.19/0.47           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['11', '13', '16'])).
% 0.19/0.47  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['1', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['11', '13', '16'])).
% 0.19/0.47  thf(t47_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47       ( r1_tarski @ ( k8_relset_1 @ A @ B @ D @ C ) @ A ) ))).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.47         ((r1_tarski @ (k8_relset_1 @ X13 @ X14 @ X15 @ X16) @ X13)
% 0.19/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.19/0.47          | ~ (v1_funct_1 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t47_funct_2])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.47          | ~ (v1_funct_1 @ X1)
% 0.19/0.47          | (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2) @ 
% 0.19/0.47             k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) @ 
% 0.19/0.47           k1_xboole_0)
% 0.19/0.47          | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['18', '21'])).
% 0.19/0.47  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (r1_tarski @ (k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) @ 
% 0.19/0.47          k1_xboole_0)),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf(t3_xboole_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((k8_relset_1 @ k1_xboole_0 @ X1 @ sk_C @ X0) = (k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '26'])).
% 0.19/0.47  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
