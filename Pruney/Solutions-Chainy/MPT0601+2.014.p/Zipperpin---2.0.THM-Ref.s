%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HgXuGytArY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  446 ( 679 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

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

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','19'])).

thf('21',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X15 ) )
        = X14 )
      | ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k9_relat_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k11_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ X16 @ ( k1_tarski @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('32',plain,
    ( ( ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HgXuGytArY
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 173 iterations in 0.082s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.53  thf(t205_relat_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) =>
% 0.19/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i]:
% 0.19/0.53        ( ( v1_relat_1 @ B ) =>
% 0.19/0.53          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.53            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.19/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf(d16_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.19/0.53          | ~ (v1_relat_1 @ X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.53  thf(t151_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) =>
% 0.19/0.53       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.53         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i]:
% 0.19/0.53         (((k9_relat_1 @ X18 @ X19) != (k1_xboole_0))
% 0.19/0.53          | (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.19/0.53          | ~ (v1_relat_1 @ X18))),
% 0.19/0.53      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.53         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.53         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['2', '6'])).
% 0.19/0.53  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.53         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.19/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.19/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('split', [status(esa)], ['11'])).
% 0.19/0.53  thf(t3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      ((![X0 : $i]:
% 0.19/0.53          (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 0.19/0.53           | ~ (r2_hidden @ sk_A @ X0)))
% 0.19/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.19/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.53             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '14'])).
% 0.19/0.53  thf(t69_enumset1, axiom,
% 0.19/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.53  thf(d2_tarski, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.53       ( ![D:$i]:
% 0.19/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.53         (((X7) != (X6))
% 0.19/0.53          | (r2_hidden @ X7 @ X8)
% 0.19/0.53          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.19/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.53  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['16', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.53       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('demod', [status(thm)], ['15', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('split', [status(esa)], ['11'])).
% 0.19/0.53  thf(t65_zfmisc_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i]:
% 0.19/0.53         (((k4_xboole_0 @ X14 @ (k1_tarski @ X15)) = (X14))
% 0.19/0.53          | (r2_hidden @ X15 @ X14))),
% 0.19/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))
% 0.19/0.53          = (k1_relat_1 @ sk_B)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.53  thf(t79_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X4 : $i, X5 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X5)),
% 0.19/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i]:
% 0.19/0.53         (~ (r1_xboole_0 @ (k1_relat_1 @ X18) @ X19)
% 0.19/0.53          | ((k9_relat_1 @ X18 @ X19) = (k1_xboole_0))
% 0.19/0.53          | ~ (v1_relat_1 @ X18))),
% 0.19/0.53      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (((~ (v1_relat_1 @ sk_B)
% 0.19/0.53         | ((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.53  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         (((k11_relat_1 @ X16 @ X17) = (k9_relat_1 @ X16 @ (k1_tarski @ X17)))
% 0.19/0.53          | ~ (v1_relat_1 @ X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.53  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('34', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.19/0.53         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.53      inference('split', [status(esa)], ['11'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.53         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.53             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.53  thf('38', plain, ($false),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '37'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
