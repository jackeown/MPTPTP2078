%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgQcNBN4A1

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   60 (  78 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 ( 570 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X60: $i] :
      ( ( ( k3_relat_1 @ X60 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X46 @ X47 ) @ X48 )
      | ( r2_hidden @ X46 @ X49 )
      | ( X49
       != ( k1_relat_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ ( k1_relat_1 @ X48 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X46 @ X47 ) @ X48 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X60: $i] :
      ( ( ( k3_relat_1 @ X60 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('17',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X53 @ X54 ) @ X55 )
      | ( r2_hidden @ X54 @ X56 )
      | ( X56
       != ( k2_relat_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('18',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k2_relat_1 @ X55 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X53 @ X54 ) @ X55 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['14','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgQcNBN4A1
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 305 iterations in 0.150s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.60  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.43/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.60  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.43/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(t30_relat_1, conjecture,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( v1_relat_1 @ C ) =>
% 0.43/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.43/0.60         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.43/0.60           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.60        ( ( v1_relat_1 @ C ) =>
% 0.43/0.60          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.43/0.60            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.43/0.60              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.43/0.60  thf('0', plain,
% 0.43/0.60      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))
% 0.43/0.60        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('1', plain,
% 0.43/0.60      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))
% 0.43/0.60         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf(d6_relat_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( v1_relat_1 @ A ) =>
% 0.43/0.60       ( ( k3_relat_1 @ A ) =
% 0.43/0.60         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      (![X60 : $i]:
% 0.43/0.60         (((k3_relat_1 @ X60)
% 0.43/0.60            = (k2_xboole_0 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60)))
% 0.43/0.60          | ~ (v1_relat_1 @ X60))),
% 0.43/0.60      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.60  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(d4_relat_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.43/0.60       ( ![C:$i]:
% 0.43/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.43/0.60         (~ (r2_hidden @ (k4_tarski @ X46 @ X47) @ X48)
% 0.43/0.60          | (r2_hidden @ X46 @ X49)
% 0.43/0.60          | ((X49) != (k1_relat_1 @ X48)))),
% 0.43/0.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.60  thf('5', plain,
% 0.43/0.60      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.43/0.60         ((r2_hidden @ X46 @ (k1_relat_1 @ X48))
% 0.43/0.60          | ~ (r2_hidden @ (k4_tarski @ X46 @ X47) @ X48))),
% 0.43/0.60      inference('simplify', [status(thm)], ['4'])).
% 0.43/0.60  thf('6', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '5'])).
% 0.43/0.60  thf(t7_xboole_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.60  thf('7', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.43/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.60  thf(d3_tarski, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.60          | (r2_hidden @ X0 @ X2)
% 0.43/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.43/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (r2_hidden @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_3) @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.43/0.60  thf('11', plain,
% 0.43/0.60      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('sup+', [status(thm)], ['2', '10'])).
% 0.43/0.60  thf('12', plain, ((v1_relat_1 @ sk_C_3)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('13', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.43/0.60  thf('14', plain,
% 0.43/0.60      (($false) <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))))),
% 0.43/0.60      inference('demod', [status(thm)], ['1', '13'])).
% 0.43/0.60  thf('15', plain,
% 0.43/0.60      (![X60 : $i]:
% 0.43/0.60         (((k3_relat_1 @ X60)
% 0.43/0.60            = (k2_xboole_0 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60)))
% 0.43/0.60          | ~ (v1_relat_1 @ X60))),
% 0.43/0.60      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.43/0.60  thf('16', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_3)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(d5_relat_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.60       ( ![C:$i]:
% 0.43/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.43/0.60         (~ (r2_hidden @ (k4_tarski @ X53 @ X54) @ X55)
% 0.43/0.60          | (r2_hidden @ X54 @ X56)
% 0.43/0.60          | ((X56) != (k2_relat_1 @ X55)))),
% 0.43/0.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.43/0.60         ((r2_hidden @ X54 @ (k2_relat_1 @ X55))
% 0.43/0.60          | ~ (r2_hidden @ (k4_tarski @ X53 @ X54) @ X55))),
% 0.43/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.43/0.60  thf('19', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('sup-', [status(thm)], ['16', '18'])).
% 0.43/0.60  thf(commutativity_k2_tarski, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.43/0.60  thf(l51_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X37 : $i, X38 : $i]:
% 0.43/0.60         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.43/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.60  thf('22', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.43/0.60  thf('23', plain,
% 0.43/0.60      (![X37 : $i, X38 : $i]:
% 0.43/0.60         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.43/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.43/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.43/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.43/0.60  thf('27', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.60          | (r2_hidden @ X0 @ X2)
% 0.43/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.60  thf('28', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.60  thf('29', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C_3)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['19', '28'])).
% 0.43/0.60  thf('30', plain,
% 0.43/0.60      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)) | ~ (v1_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('sup+', [status(thm)], ['15', '29'])).
% 0.43/0.60  thf('31', plain, ((v1_relat_1 @ sk_C_3)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('32', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))),
% 0.43/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.43/0.60  thf('33', plain,
% 0.43/0.60      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))
% 0.43/0.60         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3))))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('34', plain, (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.60  thf('35', plain,
% 0.43/0.60      (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3))) | 
% 0.43/0.60       ~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_3)))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('36', plain, (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_3)))),
% 0.43/0.60      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.43/0.60  thf('37', plain, ($false),
% 0.43/0.60      inference('simpl_trail', [status(thm)], ['14', '36'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
