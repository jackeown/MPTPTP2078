%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vcc6Yir8Kd

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:55 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  419 ( 759 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X18 @ X17 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X26 @ X25 ) @ X27 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X26 @ X27 ) @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','28','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['6','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vcc6Yir8Kd
% 0.17/0.37  % Computer   : n014.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:35:07 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 297 iterations in 0.285s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(t41_subset_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ![C:$i]:
% 0.59/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77           ( r1_tarski @
% 0.59/0.77             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.59/0.77             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i]:
% 0.59/0.77        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77          ( ![C:$i]:
% 0.59/0.77            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77              ( r1_tarski @
% 0.59/0.77                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.59/0.77                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (~ (r1_tarski @ 
% 0.59/0.77          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.59/0.77          (k3_subset_1 @ sk_A @ sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k4_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.59/0.77          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.59/0.77          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.59/0.77          (k3_subset_1 @ sk_A @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '5'])).
% 0.59/0.77  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(involutiveness_k3_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X20 : $i, X21 : $i]:
% 0.59/0.77         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.59/0.77          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.77  thf('10', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(dt_k4_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.59/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.59/0.77          | (m1_subset_1 @ (k4_subset_1 @ X18 @ X17 @ X19) @ 
% 0.59/0.77             (k1_zfmisc_1 @ X18)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.59/0.77           (k1_zfmisc_1 @ sk_A))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['10', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.77  thf(t36_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ![C:$i]:
% 0.59/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.59/0.77             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.59/0.77          | (r1_tarski @ (k3_subset_1 @ X26 @ X25) @ X27)
% 0.59/0.77          | ~ (r1_tarski @ (k3_subset_1 @ X26 @ X27) @ X25)
% 0.59/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.59/0.77               (k2_xboole_0 @ sk_B @ sk_C))
% 0.59/0.77          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.59/0.77             X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.59/0.77        | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.59/0.77           (k3_subset_1 @ sk_A @ sk_B))
% 0.59/0.77        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['9', '18'])).
% 0.59/0.77  thf(idempotence_k3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.77  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.77  thf(t22_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)) = (X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.59/0.77  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf(t46_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.77  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.77  thf(t44_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.59/0.77       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.77         ((r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.59/0.77          | ~ (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.59/0.77          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.77  thf('27', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.59/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.77  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(dt_k3_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k3_subset_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 0.59/0.77          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.59/0.77        (k3_subset_1 @ sk_A @ sk_B))),
% 0.59/0.77      inference('demod', [status(thm)], ['19', '28', '31'])).
% 0.59/0.77  thf('33', plain, ($false), inference('demod', [status(thm)], ['6', '32'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
