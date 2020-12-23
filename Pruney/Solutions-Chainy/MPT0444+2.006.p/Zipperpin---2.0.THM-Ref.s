%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RokAE5BCgB

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:46 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  263 ( 497 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['18','19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RokAE5BCgB
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.69  % Solved by: fo/fo7.sh
% 0.52/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.69  % done 515 iterations in 0.232s
% 0.52/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.69  % SZS output start Refutation
% 0.52/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.69  thf('0', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.69  thf(t48_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.69  thf('1', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.52/0.69           = (k3_xboole_0 @ X7 @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.69  thf(t36_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.69  thf('2', plain,
% 0.52/0.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.52/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.69  thf('3', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.52/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.69  thf(t25_relat_1, axiom,
% 0.52/0.69    (![A:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ A ) =>
% 0.52/0.69       ( ![B:$i]:
% 0.52/0.69         ( ( v1_relat_1 @ B ) =>
% 0.52/0.69           ( ( r1_tarski @ A @ B ) =>
% 0.52/0.69             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.52/0.69               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.52/0.69  thf('4', plain,
% 0.52/0.69      (![X21 : $i, X22 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X21)
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ X22) @ (k2_relat_1 @ X21))
% 0.52/0.69          | ~ (r1_tarski @ X22 @ X21)
% 0.52/0.69          | ~ (v1_relat_1 @ X22))),
% 0.52/0.69      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.52/0.69  thf('5', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.52/0.69             (k2_relat_1 @ X0))
% 0.52/0.69          | ~ (v1_relat_1 @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.69  thf('6', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.52/0.69      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.69  thf(t3_subset, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.69  thf('7', plain,
% 0.52/0.69      (![X16 : $i, X18 : $i]:
% 0.52/0.69         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.69  thf('8', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.69  thf(cc2_relat_1, axiom,
% 0.52/0.69    (![A:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ A ) =>
% 0.52/0.69       ( ![B:$i]:
% 0.52/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.69  thf('9', plain,
% 0.52/0.69      (![X19 : $i, X20 : $i]:
% 0.52/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.52/0.69          | (v1_relat_1 @ X19)
% 0.52/0.69          | ~ (v1_relat_1 @ X20))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.69  thf('10', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.69  thf('11', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X0)
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.52/0.69             (k2_relat_1 @ X0)))),
% 0.52/0.69      inference('clc', [status(thm)], ['5', '10'])).
% 0.52/0.69  thf('12', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.69           (k2_relat_1 @ X0))
% 0.52/0.69          | ~ (v1_relat_1 @ X0))),
% 0.52/0.69      inference('sup+', [status(thm)], ['0', '11'])).
% 0.52/0.69  thf('13', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X0)
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.52/0.69             (k2_relat_1 @ X0)))),
% 0.52/0.69      inference('clc', [status(thm)], ['5', '10'])).
% 0.52/0.69  thf(t19_xboole_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.52/0.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.69  thf('14', plain,
% 0.52/0.69      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.69         (~ (r1_tarski @ X2 @ X3)
% 0.52/0.69          | ~ (r1_tarski @ X2 @ X4)
% 0.52/0.69          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.52/0.69  thf('15', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X0)
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.52/0.69             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 0.52/0.69          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.52/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.69  thf('16', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ X0)
% 0.52/0.69          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.69             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.52/0.69          | ~ (v1_relat_1 @ X1))),
% 0.52/0.69      inference('sup-', [status(thm)], ['12', '15'])).
% 0.52/0.69  thf(t27_relat_1, conjecture,
% 0.52/0.69    (![A:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ A ) =>
% 0.52/0.69       ( ![B:$i]:
% 0.52/0.69         ( ( v1_relat_1 @ B ) =>
% 0.52/0.69           ( r1_tarski @
% 0.52/0.69             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.52/0.69             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.52/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.69    (~( ![A:$i]:
% 0.52/0.69        ( ( v1_relat_1 @ A ) =>
% 0.52/0.69          ( ![B:$i]:
% 0.52/0.69            ( ( v1_relat_1 @ B ) =>
% 0.52/0.69              ( r1_tarski @
% 0.52/0.69                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.52/0.69                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.52/0.69    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.52/0.69  thf('17', plain,
% 0.52/0.69      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.52/0.69          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('18', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.52/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.69  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('21', plain, ($false),
% 0.52/0.69      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.52/0.69  
% 0.52/0.69  % SZS output end Refutation
% 0.52/0.69  
% 0.52/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
