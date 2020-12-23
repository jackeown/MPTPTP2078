%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0ZVKrIHBK

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:01 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 140 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  624 (1154 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( ( k1_ordinal1 @ X23 )
      = ( k2_xboole_0 @ X23 @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( r1_ordinal1 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( sk_A = sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( r1_ordinal1 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    ! [X23: $i] :
      ( ( k1_ordinal1 @ X23 )
      = ( k2_xboole_0 @ X23 @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v3_ordinal1 @ X26 )
      | ( r1_ordinal1 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ X27 )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('37',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_ordinal1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ~ ( v3_ordinal1 @ X25 )
      | ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_ordinal1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('52',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i] :
      ( ( k1_ordinal1 @ X23 )
      = ( k2_xboole_0 @ X23 @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('63',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0ZVKrIHBK
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 592 iterations in 0.317s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.59/0.76  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.59/0.76  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.59/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(t34_ordinal1, conjecture,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v3_ordinal1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( v3_ordinal1 @ B ) =>
% 0.59/0.76           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.59/0.76             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i]:
% 0.59/0.76        ( ( v3_ordinal1 @ A ) =>
% 0.59/0.76          ( ![B:$i]:
% 0.59/0.76            ( ( v3_ordinal1 @ B ) =>
% 0.59/0.76              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.59/0.76                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.59/0.76        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.59/0.76       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.76      inference('split', [status(esa)], ['0'])).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.59/0.76         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.76      inference('split', [status(esa)], ['2'])).
% 0.59/0.76  thf(d1_ordinal1, axiom,
% 0.59/0.76    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (![X23 : $i]:
% 0.59/0.76         ((k1_ordinal1 @ X23) = (k2_xboole_0 @ X23 @ (k1_tarski @ X23)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.59/0.76  thf(d3_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.59/0.76       ( ![D:$i]:
% 0.59/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.76           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.76          | (r2_hidden @ X6 @ X5)
% 0.59/0.76          | (r2_hidden @ X6 @ X3)
% 0.59/0.76          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.76  thf('6', plain,
% 0.59/0.76      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.59/0.76         ((r2_hidden @ X6 @ X3)
% 0.59/0.76          | (r2_hidden @ X6 @ X5)
% 0.59/0.76          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.59/0.76          | (r2_hidden @ X1 @ X0)
% 0.59/0.76          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['4', '6'])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.77      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.59/0.77         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '7'])).
% 0.59/0.77  thf(d1_tarski, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X14 @ X13)
% 0.59/0.77          | ((X14) = (X11))
% 0.59/0.77          | ((X13) != (k1_tarski @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X11 : $i, X14 : $i]:
% 0.59/0.77         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.59/0.77         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['8', '10'])).
% 0.59/0.77  thf(t26_ordinal1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v3_ordinal1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v3_ordinal1 @ B ) =>
% 0.59/0.77           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X26)
% 0.59/0.77          | (r1_ordinal1 @ X27 @ X26)
% 0.59/0.77          | (r2_hidden @ X26 @ X27)
% 0.59/0.77          | ~ (v3_ordinal1 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.59/0.77  thf(antisymmetry_r2_hidden, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (((((sk_A) = (sk_B))
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_B)
% 0.59/0.77         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_A)))
% 0.59/0.77         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '14'])).
% 0.59/0.77  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.59/0.77         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      ((((sk_A) = (sk_B)))
% 0.59/0.77         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.59/0.77             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.59/0.77         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.59/0.77             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X26)
% 0.59/0.77          | (r1_ordinal1 @ X27 @ X26)
% 0.59/0.77          | (r2_hidden @ X26 @ X27)
% 0.59/0.77          | ~ (v3_ordinal1 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X1 @ X0)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r1_ordinal1 @ X1 @ X0)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ sk_A)
% 0.59/0.77          | (r1_ordinal1 @ sk_A @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['23', '27'])).
% 0.59/0.77  thf('29', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 0.59/0.77      inference('eq_fact', [status(thm)], ['28'])).
% 0.59/0.77  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('31', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.59/0.77       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['22', '31'])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.59/0.77       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['2'])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X23 : $i]:
% 0.59/0.77         ((k1_ordinal1 @ X23) = (k2_xboole_0 @ X23 @ (k1_tarski @ X23)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X26)
% 0.59/0.77          | (r1_ordinal1 @ X27 @ X26)
% 0.59/0.77          | (r2_hidden @ X26 @ X27)
% 0.59/0.77          | ~ (v3_ordinal1 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X2 @ X5)
% 0.59/0.77          | (r2_hidden @ X2 @ X4)
% 0.59/0.77          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.59/0.77         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.59/0.77      inference('simplify', [status(thm)], ['36'])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X0)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['35', '37'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.59/0.77          | ~ (v3_ordinal1 @ X1)
% 0.59/0.77          | (r1_ordinal1 @ X0 @ X1)
% 0.59/0.77          | ~ (v3_ordinal1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['34', '38'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (((~ (v3_ordinal1 @ sk_B)
% 0.59/0.77         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_A)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.77  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.59/0.77  thf(redefinition_r1_ordinal1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.59/0.77       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.59/0.77  thf('45', plain,
% 0.59/0.77      (![X24 : $i, X25 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X24)
% 0.59/0.77          | ~ (v3_ordinal1 @ X25)
% 0.59/0.77          | (r1_tarski @ X24 @ X25)
% 0.59/0.77          | ~ (r1_ordinal1 @ X24 @ X25))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      ((((r1_tarski @ sk_B @ sk_A)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_A)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_B)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.59/0.77  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('48', plain, ((v3_ordinal1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (((r1_tarski @ sk_B @ sk_A))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.59/0.77  thf('50', plain,
% 0.59/0.77      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['2'])).
% 0.59/0.77  thf('51', plain,
% 0.59/0.77      (![X24 : $i, X25 : $i]:
% 0.59/0.77         (~ (v3_ordinal1 @ X24)
% 0.59/0.77          | ~ (v3_ordinal1 @ X25)
% 0.59/0.77          | (r1_tarski @ X24 @ X25)
% 0.59/0.77          | ~ (r1_ordinal1 @ X24 @ X25))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      ((((r1_tarski @ sk_A @ sk_B)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_B)
% 0.59/0.77         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.77  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.59/0.77  thf(d10_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      (![X8 : $i, X10 : $i]:
% 0.59/0.77         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.59/0.77         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      ((((sk_B) = (sk_A)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.59/0.77             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['49', '57'])).
% 0.59/0.77  thf('59', plain,
% 0.59/0.77      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('60', plain,
% 0.59/0.77      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.59/0.77         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.59/0.77             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (![X23 : $i]:
% 0.59/0.77         ((k1_ordinal1 @ X23) = (k2_xboole_0 @ X23 @ (k1_tarski @ X23)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.59/0.77  thf('62', plain,
% 0.59/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.77         (((X12) != (X11))
% 0.59/0.77          | (r2_hidden @ X12 @ X13)
% 0.59/0.77          | ((X13) != (k1_tarski @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.77  thf('63', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 0.59/0.77      inference('simplify', [status(thm)], ['62'])).
% 0.59/0.77  thf('64', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X2 @ X3)
% 0.59/0.77          | (r2_hidden @ X2 @ X4)
% 0.59/0.77          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.59/0.77         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.77      inference('simplify', [status(thm)], ['64'])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['63', '65'])).
% 0.59/0.77  thf('67', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['61', '66'])).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.59/0.77       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['60', '67'])).
% 0.59/0.77  thf('69', plain, ($false),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '68'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
