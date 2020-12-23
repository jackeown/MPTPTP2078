%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxcDfHUVRG

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:13 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 ( 708 expanded)
%              Number of equality atoms :   45 (  80 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_2 ) @ sk_A )
    = ( k1_tarski @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k3_xboole_0 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_2 ) )
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_D_2 )
    = ( k3_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','36'])).

thf('38',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_2 )
 != ( k1_tarski @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_C_2 @ sk_A )
 != ( k1_tarski @ sk_D_2 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxcDfHUVRG
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:39:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 199 iterations in 0.095s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.53  thf(t148_zfmisc_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53     ( ( ( r1_tarski @ A @ B ) & 
% 0.19/0.53         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.19/0.53         ( r2_hidden @ D @ A ) ) =>
% 0.19/0.53       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.53        ( ( ( r1_tarski @ A @ B ) & 
% 0.19/0.53            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.19/0.53            ( r2_hidden @ D @ A ) ) =>
% 0.19/0.53          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.19/0.53  thf('0', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d3_tarski, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X3 : $i, X5 : $i]:
% 0.19/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.53  thf(d1_tarski, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X26 @ X25)
% 0.19/0.53          | ((X26) = (X23))
% 0.19/0.53          | ((X25) != (k1_tarski @ X23)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X23 : $i, X26 : $i]:
% 0.19/0.53         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X3 : $i, X5 : $i]:
% 0.19/0.53         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.19/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.53  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_D_2) @ sk_A)),
% 0.19/0.53      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.53  thf(t28_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_D_2) @ sk_A) = (k1_tarski @ sk_D_2))),
% 0.19/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2)) = (k1_tarski @ sk_D_2))),
% 0.19/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_tarski @ sk_D_2))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X19 : $i, X20 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.19/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.53  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.53  thf(t16_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.53       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.53           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ sk_A @ X0)
% 0.19/0.53           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.53  thf('23', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.53           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.19/0.53           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.19/0.53              (k3_xboole_0 @ sk_A @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['21', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.53           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.53           = (k3_xboole_0 @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.53           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 0.19/0.53           = (k3_xboole_0 @ sk_A @ X0))),
% 0.19/0.53      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.19/0.53  thf('33', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.19/0.53           = (k3_xboole_0 @ sk_A @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['14', '32'])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2))
% 0.19/0.53         = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.19/0.53      inference('sup+', [status(thm)], ['13', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.54      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_2))
% 0.19/0.54         = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.54  thf('37', plain, (((k1_tarski @ sk_D_2) = (k3_xboole_0 @ sk_C_2 @ sk_A))),
% 0.19/0.54      inference('sup+', [status(thm)], ['12', '36'])).
% 0.19/0.54  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) != (k1_tarski @ sk_D_2))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.54  thf('40', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) != (k1_tarski @ sk_D_2))),
% 0.19/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.54  thf('41', plain, ($false),
% 0.19/0.54      inference('simplify_reflect-', [status(thm)], ['37', '40'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
