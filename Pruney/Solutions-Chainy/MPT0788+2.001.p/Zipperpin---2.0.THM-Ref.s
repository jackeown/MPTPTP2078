%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v4YekEcFSQ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 192 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  644 (3111 expanded)
%              Number of equality atoms :   26 ( 133 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t38_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
         => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
          <=> ( ( A = B )
              | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_wellord1])).

thf('0',plain,
    ( ( sk_A != sk_B )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ( sk_A = sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X9 @ X10 ) @ ( k1_wellord1 @ X9 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
      | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) )
      | ~ ( v2_wellord1 @ sk_C ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_wellord1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( X6
       != ( k1_wellord1 @ X5 @ X4 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X4 ) @ X5 )
      | ( X8 = X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( X8 = X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X4 ) @ X5 )
      | ( r2_hidden @ X8 @ ( k1_wellord1 @ X5 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
      | ( sk_A = sk_B )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
      | ( sk_A = sk_B ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != sk_B )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_A != sk_B )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_A ) )
   <= ( ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['20','26'])).

thf('28',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['19','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['3','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k1_wellord1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X5 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_A != sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['20','40','3','31','41'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['39','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ( r1_tarski @ ( k1_wellord1 @ X9 @ X10 ) @ ( k1_wellord1 @ X9 @ X11 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C ) )
      | ~ ( v2_wellord1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_wellord1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C @ sk_A ) @ ( k1_wellord1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['33','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v4YekEcFSQ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 61 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.49  thf(t38_wellord1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.49         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.20/0.49           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ C ) =>
% 0.20/0.49          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.49            ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.20/0.49              ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t38_wellord1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_A) != (sk_B))
% 0.20/0.49        | ~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))
% 0.20/0.49        | ~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B))) | 
% 0.20/0.49       ~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))
% 0.20/0.49        | ((sk_A) = (sk_B))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf(t37_wellord1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.20/0.49         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X9)
% 0.20/0.49          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.20/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.20/0.49          | ~ (r1_tarski @ (k1_wellord1 @ X9 @ X10) @ (k1_wellord1 @ X9 @ X11))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C)
% 0.20/0.49         | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.49         | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C))
% 0.20/0.49         | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))
% 0.20/0.49         | ~ (v2_wellord1 @ sk_C)))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain, ((v2_wellord1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.20/0.49  thf(d1_wellord1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i,C:$i]:
% 0.20/0.49         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.20/0.49           ( ![D:$i]:
% 0.20/0.49             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.49         (((X6) != (k1_wellord1 @ X5 @ X4))
% 0.20/0.49          | (r2_hidden @ X8 @ X6)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X8 @ X4) @ X5)
% 0.20/0.49          | ((X8) = (X4))
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ((X8) = (X4))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X8 @ X4) @ X5)
% 0.20/0.49          | (r2_hidden @ X8 @ (k1_wellord1 @ X5 @ X4)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))
% 0.20/0.49         | ((sk_A) = (sk_B))
% 0.20/0.49         | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.49  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)) | ((sk_A) = (sk_B))))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((sk_A) != (sk_B))
% 0.20/0.49        | ~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('21', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C @ sk_A)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))) & 
% 0.20/0.49             (((sk_A) = (sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B))) | 
% 0.20/0.49       ~ (((sk_A) = (sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('27', plain, (~ (((sk_A) = (sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['20', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['19', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49               (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['17', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['3', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (~ (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) != (k1_wellord1 @ X5 @ X4))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X7 @ X4) @ X5)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X6)
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X5 @ X4))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X7 @ X4) @ X5))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C) | ~ (v1_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '36'])).
% 0.20/0.49  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B))) | 
% 0.20/0.49       ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B))) | 
% 0.20/0.49       (((sk_A) = (sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('42', plain, (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['20', '40', '3', '31', '41'])).
% 0.20/0.49  thf('43', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['39', '42'])).
% 0.20/0.49  thf('44', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X9)
% 0.20/0.49          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.20/0.49          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ X9 @ X10) @ (k1_wellord1 @ X9 @ X11))
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49             (k1_wellord1 @ sk_C @ X0))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C))
% 0.20/0.49          | ~ (v2_wellord1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('48', plain, ((v2_wellord1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ X0))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C))
% 0.20/0.49        | (r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ 
% 0.20/0.49           (k1_wellord1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '49'])).
% 0.20/0.49  thf('51', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      ((r1_tarski @ (k1_wellord1 @ sk_C @ sk_A) @ (k1_wellord1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain, ($false), inference('demod', [status(thm)], ['33', '52'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
