%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EKzaDh1xuD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   67 (  86 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  433 ( 652 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ sk_A )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_C_2 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','32'])).

thf('34',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['8','37'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EKzaDh1xuD
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.27/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.48  % Solved by: fo/fo7.sh
% 1.27/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.48  % done 3411 iterations in 1.015s
% 1.27/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.48  % SZS output start Refutation
% 1.27/1.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.27/1.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.27/1.48  thf(sk_D_type, type, sk_D: $i).
% 1.27/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.48  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.27/1.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.27/1.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.27/1.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.27/1.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.48  thf(t149_zfmisc_1, conjecture,
% 1.27/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.27/1.48         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.27/1.48       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.27/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.48        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.27/1.48            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.27/1.48          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.27/1.48    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.27/1.48  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(d7_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.27/1.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.27/1.48  thf('2', plain,
% 1.27/1.48      (![X2 : $i, X3 : $i]:
% 1.27/1.48         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.27/1.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.48  thf('3', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['1', '2'])).
% 1.27/1.48  thf(commutativity_k3_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.27/1.48  thf('4', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.48  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.27/1.48      inference('demod', [status(thm)], ['3', '4'])).
% 1.27/1.48  thf('6', plain,
% 1.27/1.48      (![X2 : $i, X4 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.27/1.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.48  thf('7', plain,
% 1.27/1.48      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_2))),
% 1.27/1.48      inference('sup-', [status(thm)], ['5', '6'])).
% 1.27/1.48  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.27/1.48      inference('simplify', [status(thm)], ['7'])).
% 1.27/1.48  thf(t17_xboole_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.27/1.48  thf('9', plain,
% 1.27/1.48      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 1.27/1.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.27/1.48  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.27/1.48      inference('demod', [status(thm)], ['3', '4'])).
% 1.27/1.48  thf('11', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.48  thf(t77_xboole_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.27/1.48          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.27/1.48  thf('12', plain,
% 1.27/1.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ X24 @ X25)
% 1.27/1.48          | ~ (r1_xboole_0 @ X24 @ (k3_xboole_0 @ X25 @ X26))
% 1.27/1.48          | ~ (r1_tarski @ X24 @ X26))),
% 1.27/1.48      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.27/1.48  thf('13', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.48          | ~ (r1_tarski @ X2 @ X1)
% 1.27/1.48          | (r1_xboole_0 @ X2 @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['11', '12'])).
% 1.27/1.48  thf('14', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.27/1.48          | (r1_xboole_0 @ X0 @ sk_C_2)
% 1.27/1.48          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.27/1.48      inference('sup-', [status(thm)], ['10', '13'])).
% 1.27/1.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.27/1.48  thf('15', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 1.27/1.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.27/1.48  thf('16', plain,
% 1.27/1.48      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_2) | ~ (r1_tarski @ X0 @ sk_B))),
% 1.27/1.48      inference('demod', [status(thm)], ['14', '15'])).
% 1.27/1.48  thf('17', plain,
% 1.27/1.48      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_2)),
% 1.27/1.48      inference('sup-', [status(thm)], ['9', '16'])).
% 1.27/1.48  thf(t4_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.27/1.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.27/1.48  thf('18', plain,
% 1.27/1.48      (![X11 : $i, X12 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ X11 @ X12)
% 1.27/1.48          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 1.27/1.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.27/1.48  thf(l27_zfmisc_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.27/1.48  thf('19', plain,
% 1.27/1.48      (![X33 : $i, X34 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 1.27/1.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.27/1.48  thf('20', plain,
% 1.27/1.48      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('21', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.48  thf('22', plain,
% 1.27/1.48      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.27/1.48      inference('demod', [status(thm)], ['20', '21'])).
% 1.27/1.48  thf(t28_xboole_1, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.27/1.48  thf('23', plain,
% 1.27/1.48      (![X17 : $i, X18 : $i]:
% 1.27/1.48         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.27/1.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.27/1.48  thf('24', plain,
% 1.27/1.48      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.27/1.48         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.48      inference('sup-', [status(thm)], ['22', '23'])).
% 1.27/1.48  thf('25', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.48  thf('26', plain,
% 1.27/1.48      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.48         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.48      inference('demod', [status(thm)], ['24', '25'])).
% 1.27/1.48  thf('27', plain,
% 1.27/1.48      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.27/1.48         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 1.27/1.48          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.27/1.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.27/1.48  thf('28', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.48          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['26', '27'])).
% 1.27/1.48  thf('29', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.48          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['19', '28'])).
% 1.27/1.48  thf('30', plain,
% 1.27/1.48      (((r1_xboole_0 @ sk_B @ sk_A)
% 1.27/1.48        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['18', '29'])).
% 1.27/1.48  thf(t3_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.27/1.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.27/1.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.27/1.48  thf('31', plain,
% 1.27/1.48      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.27/1.48         (~ (r2_hidden @ X9 @ X7)
% 1.27/1.48          | ~ (r2_hidden @ X9 @ X10)
% 1.27/1.48          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.27/1.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.27/1.48  thf('32', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ sk_B @ sk_A)
% 1.27/1.48          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.27/1.48          | ~ (r2_hidden @ sk_D @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['30', '31'])).
% 1.27/1.48  thf('33', plain,
% 1.27/1.48      ((~ (r2_hidden @ sk_D @ sk_C_2) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.48      inference('sup-', [status(thm)], ['17', '32'])).
% 1.27/1.48  thf('34', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.27/1.48      inference('demod', [status(thm)], ['33', '34'])).
% 1.27/1.48  thf(t70_xboole_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.27/1.48            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.27/1.48       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.27/1.48            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.27/1.48  thf('36', plain,
% 1.27/1.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 1.27/1.48          | ~ (r1_xboole_0 @ X20 @ X21)
% 1.27/1.48          | ~ (r1_xboole_0 @ X20 @ X22))),
% 1.27/1.48      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.27/1.48  thf('37', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.27/1.48          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['35', '36'])).
% 1.27/1.48  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.27/1.48      inference('sup-', [status(thm)], ['8', '37'])).
% 1.27/1.48  thf(symmetry_r1_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.27/1.48  thf('39', plain,
% 1.27/1.48      (![X5 : $i, X6 : $i]:
% 1.27/1.48         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.27/1.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.27/1.48  thf('40', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.27/1.48      inference('sup-', [status(thm)], ['38', '39'])).
% 1.27/1.48  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 1.27/1.48  
% 1.27/1.48  % SZS output end Refutation
% 1.27/1.48  
% 1.27/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
