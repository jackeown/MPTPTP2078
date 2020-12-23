%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M5V1QRLTol

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:07 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 140 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  649 (1143 expanded)
%              Number of equality atoms :   35 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_ordinal1 @ X64 @ X65 )
      | ( r1_ordinal1 @ X65 @ X64 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v3_ordinal1 @ X67 )
      | ~ ( v3_ordinal1 @ X68 )
      | ( r1_tarski @ X67 @ X68 )
      | ~ ( r1_ordinal1 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
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

thf('22',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('40',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v3_ordinal1 @ X67 )
      | ~ ( v3_ordinal1 @ X68 )
      | ( r1_tarski @ X67 @ X68 )
      | ~ ( r1_ordinal1 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ( r2_hidden @ X70 @ X69 )
      | ( X70 = X69 )
      | ( r2_hidden @ X69 @ X70 )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('46',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_A )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('63',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M5V1QRLTol
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 608 iterations in 0.233s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.68  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.68  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.49/0.68  thf(t34_ordinal1, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.68           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.49/0.68             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( v3_ordinal1 @ A ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( v3_ordinal1 @ B ) =>
% 0.49/0.68              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.49/0.68                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.49/0.68        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.49/0.68       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(connectedness_r1_ordinal1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.49/0.68       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X64 : $i, X65 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X64)
% 0.49/0.68          | ~ (v3_ordinal1 @ X65)
% 0.49/0.68          | (r1_ordinal1 @ X64 @ X65)
% 0.49/0.68          | (r1_ordinal1 @ X65 @ X64))),
% 0.49/0.68      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_ordinal1 @ X0 @ sk_A)
% 0.49/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.49/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf(redefinition_r1_ordinal1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.49/0.68       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X67 : $i, X68 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X67)
% 0.49/0.68          | ~ (v3_ordinal1 @ X68)
% 0.49/0.68          | (r1_tarski @ X67 @ X68)
% 0.49/0.68          | ~ (r1_ordinal1 @ X67 @ X68))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X0)
% 0.49/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.49/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.49/0.68          | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.68  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X0)
% 0.49/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.49/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.49/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ X0 @ sk_A)
% 0.49/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.49/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_B @ sk_A)))
% 0.49/0.68         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.68  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['11', '12'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['14'])).
% 0.49/0.68  thf(d1_ordinal1, axiom,
% 0.49/0.68    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X66 : $i]:
% 0.49/0.68         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.49/0.68  thf(d3_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.49/0.68       ( ![D:$i]:
% 0.49/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.68           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X4 @ X2)
% 0.49/0.68          | (r2_hidden @ X4 @ X3)
% 0.49/0.68          | (r2_hidden @ X4 @ X1)
% 0.49/0.68          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.49/0.68         ((r2_hidden @ X4 @ X1)
% 0.49/0.68          | (r2_hidden @ X4 @ X3)
% 0.49/0.68          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.68          | (r2_hidden @ X1 @ X0)
% 0.49/0.68          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['16', '18'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['15', '19'])).
% 0.49/0.68  thf(t69_enumset1, axiom,
% 0.49/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.68  thf(d2_tarski, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.49/0.68       ( ![D:$i]:
% 0.49/0.68         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X10 @ X8)
% 0.49/0.68          | ((X10) = (X9))
% 0.49/0.68          | ((X10) = (X6))
% 0.49/0.68          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d2_tarski])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X6 : $i, X9 : $i, X10 : $i]:
% 0.49/0.68         (((X10) = (X6))
% 0.49/0.68          | ((X10) = (X9))
% 0.49/0.68          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '23'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.49/0.68         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '25'])).
% 0.49/0.68  thf(t7_ordinal1, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X71 : $i, X72 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 0.49/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.49/0.68         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      ((((sk_A) = (sk_B)))
% 0.49/0.68         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.49/0.68             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['13', '28'])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.49/0.68         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.49/0.68             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_ordinal1 @ X0 @ sk_A)
% 0.49/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.49/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('33', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.49/0.68      inference('eq_fact', [status(thm)], ['32'])).
% 0.49/0.68  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('35', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.49/0.68       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['31', '35'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.49/0.68       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['14'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X66 : $i]:
% 0.49/0.68         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['14'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X67 : $i, X68 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X67)
% 0.49/0.68          | ~ (v3_ordinal1 @ X68)
% 0.49/0.68          | (r1_tarski @ X67 @ X68)
% 0.49/0.68          | ~ (r1_ordinal1 @ X67 @ X68))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      ((((r1_tarski @ sk_A @ sk_B)
% 0.49/0.68         | ~ (v3_ordinal1 @ sk_B)
% 0.49/0.68         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.68  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.49/0.68  thf(t24_ordinal1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.68           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.49/0.68                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X69 : $i, X70 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X69)
% 0.49/0.68          | (r2_hidden @ X70 @ X69)
% 0.49/0.68          | ((X70) = (X69))
% 0.49/0.68          | (r2_hidden @ X69 @ X70)
% 0.49/0.68          | ~ (v3_ordinal1 @ X70))),
% 0.49/0.68      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X71 : $i, X72 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 0.49/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v3_ordinal1 @ X1)
% 0.49/0.68          | (r2_hidden @ X0 @ X1)
% 0.49/0.68          | ((X1) = (X0))
% 0.49/0.68          | ~ (v3_ordinal1 @ X0)
% 0.49/0.68          | ~ (r1_tarski @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (((~ (v3_ordinal1 @ sk_A)
% 0.49/0.68         | ((sk_B) = (sk_A))
% 0.49/0.68         | (r2_hidden @ sk_A @ sk_B)
% 0.49/0.68         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['44', '47'])).
% 0.49/0.68  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.49/0.68         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X0 @ X3)
% 0.49/0.68          | (r2_hidden @ X0 @ X2)
% 0.49/0.68          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.49/0.68         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.49/0.68      inference('simplify', [status(thm)], ['52'])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      ((![X0 : $i]:
% 0.49/0.68          (((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.49/0.68         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['51', '53'])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_B) = (sk_A))))
% 0.49/0.68         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['38', '54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.49/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      ((((sk_B) = (sk_A)))
% 0.49/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.49/0.68             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.49/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.49/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.49/0.68             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      (![X66 : $i]:
% 0.49/0.68         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.68         (((X7) != (X6))
% 0.49/0.68          | (r2_hidden @ X7 @ X8)
% 0.49/0.68          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d2_tarski])).
% 0.49/0.68  thf('63', plain,
% 0.49/0.68      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 0.49/0.68      inference('simplify', [status(thm)], ['62'])).
% 0.49/0.68  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['61', '63'])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.68          | (r2_hidden @ X0 @ X2)
% 0.49/0.68          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.49/0.68         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.49/0.68      inference('simplify', [status(thm)], ['65'])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['64', '66'])).
% 0.49/0.68  thf('68', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['60', '67'])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.49/0.68       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['59', '68'])).
% 0.49/0.68  thf('70', plain, ($false),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '69'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
