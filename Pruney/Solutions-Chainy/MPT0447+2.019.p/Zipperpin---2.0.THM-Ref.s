%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3piTlWlOMO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 17.60s
% Output     : Refutation 17.60s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 117 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  603 ( 973 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k1_relat_1 @ X34 ) @ ( k1_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_D_2 @ X29 @ X27 ) ) @ X27 )
      | ( X28
       != ( k1_relat_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ ( sk_D_2 @ X29 @ X27 ) ) @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X35 @ X36 ) @ X37 )
      | ( r2_hidden @ X35 @ ( k3_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ( r1_tarski @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k3_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3piTlWlOMO
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.60/17.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.60/17.87  % Solved by: fo/fo7.sh
% 17.60/17.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.60/17.87  % done 16081 iterations in 17.418s
% 17.60/17.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.60/17.87  % SZS output start Refutation
% 17.60/17.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.60/17.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.60/17.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.60/17.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.60/17.87  thf(sk_A_type, type, sk_A: $i).
% 17.60/17.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.60/17.87  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 17.60/17.87  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 17.60/17.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.60/17.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.60/17.87  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 17.60/17.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.60/17.87  thf(sk_B_type, type, sk_B: $i).
% 17.60/17.87  thf(t31_relat_1, conjecture,
% 17.60/17.87    (![A:$i]:
% 17.60/17.87     ( ( v1_relat_1 @ A ) =>
% 17.60/17.87       ( ![B:$i]:
% 17.60/17.87         ( ( v1_relat_1 @ B ) =>
% 17.60/17.87           ( ( r1_tarski @ A @ B ) =>
% 17.60/17.87             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 17.60/17.87  thf(zf_stmt_0, negated_conjecture,
% 17.60/17.87    (~( ![A:$i]:
% 17.60/17.87        ( ( v1_relat_1 @ A ) =>
% 17.60/17.87          ( ![B:$i]:
% 17.60/17.87            ( ( v1_relat_1 @ B ) =>
% 17.60/17.87              ( ( r1_tarski @ A @ B ) =>
% 17.60/17.87                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 17.60/17.87    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 17.60/17.87  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf(d6_relat_1, axiom,
% 17.60/17.87    (![A:$i]:
% 17.60/17.87     ( ( v1_relat_1 @ A ) =>
% 17.60/17.87       ( ( k3_relat_1 @ A ) =
% 17.60/17.87         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 17.60/17.87  thf('1', plain,
% 17.60/17.87      (![X32 : $i]:
% 17.60/17.87         (((k3_relat_1 @ X32)
% 17.60/17.87            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 17.60/17.87          | ~ (v1_relat_1 @ X32))),
% 17.60/17.87      inference('cnf', [status(esa)], [d6_relat_1])).
% 17.60/17.87  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf(t25_relat_1, axiom,
% 17.60/17.87    (![A:$i]:
% 17.60/17.87     ( ( v1_relat_1 @ A ) =>
% 17.60/17.87       ( ![B:$i]:
% 17.60/17.87         ( ( v1_relat_1 @ B ) =>
% 17.60/17.87           ( ( r1_tarski @ A @ B ) =>
% 17.60/17.87             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 17.60/17.87               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 17.60/17.87  thf('3', plain,
% 17.60/17.87      (![X33 : $i, X34 : $i]:
% 17.60/17.87         (~ (v1_relat_1 @ X33)
% 17.60/17.87          | (r1_tarski @ (k1_relat_1 @ X34) @ (k1_relat_1 @ X33))
% 17.60/17.87          | ~ (r1_tarski @ X34 @ X33)
% 17.60/17.87          | ~ (v1_relat_1 @ X34))),
% 17.60/17.87      inference('cnf', [status(esa)], [t25_relat_1])).
% 17.60/17.87  thf('4', plain,
% 17.60/17.87      ((~ (v1_relat_1 @ sk_A)
% 17.60/17.87        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 17.60/17.87        | ~ (v1_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup-', [status(thm)], ['2', '3'])).
% 17.60/17.87  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('7', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 17.60/17.87      inference('demod', [status(thm)], ['4', '5', '6'])).
% 17.60/17.87  thf(t28_xboole_1, axiom,
% 17.60/17.87    (![A:$i,B:$i]:
% 17.60/17.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 17.60/17.87  thf('8', plain,
% 17.60/17.87      (![X13 : $i, X14 : $i]:
% 17.60/17.87         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 17.60/17.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.60/17.87  thf('9', plain,
% 17.60/17.87      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 17.60/17.87         = (k1_relat_1 @ sk_A))),
% 17.60/17.87      inference('sup-', [status(thm)], ['7', '8'])).
% 17.60/17.87  thf(d3_tarski, axiom,
% 17.60/17.87    (![A:$i,B:$i]:
% 17.60/17.87     ( ( r1_tarski @ A @ B ) <=>
% 17.60/17.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.60/17.87  thf('10', plain,
% 17.60/17.87      (![X1 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.60/17.87      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.87  thf(d4_relat_1, axiom,
% 17.60/17.87    (![A:$i,B:$i]:
% 17.60/17.87     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 17.60/17.87       ( ![C:$i]:
% 17.60/17.87         ( ( r2_hidden @ C @ B ) <=>
% 17.60/17.87           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 17.60/17.87  thf('11', plain,
% 17.60/17.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 17.60/17.87         (~ (r2_hidden @ X29 @ X28)
% 17.60/17.87          | (r2_hidden @ (k4_tarski @ X29 @ (sk_D_2 @ X29 @ X27)) @ X27)
% 17.60/17.87          | ((X28) != (k1_relat_1 @ X27)))),
% 17.60/17.87      inference('cnf', [status(esa)], [d4_relat_1])).
% 17.60/17.87  thf('12', plain,
% 17.60/17.87      (![X27 : $i, X29 : $i]:
% 17.60/17.87         ((r2_hidden @ (k4_tarski @ X29 @ (sk_D_2 @ X29 @ X27)) @ X27)
% 17.60/17.87          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X27)))),
% 17.60/17.87      inference('simplify', [status(thm)], ['11'])).
% 17.60/17.87  thf('13', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i]:
% 17.60/17.87         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 17.60/17.87          | (r2_hidden @ 
% 17.60/17.87             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 17.60/17.87              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 17.60/17.87             X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['10', '12'])).
% 17.60/17.87  thf(t30_relat_1, axiom,
% 17.60/17.87    (![A:$i,B:$i,C:$i]:
% 17.60/17.87     ( ( v1_relat_1 @ C ) =>
% 17.60/17.87       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 17.60/17.87         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 17.60/17.87           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 17.60/17.87  thf('14', plain,
% 17.60/17.87      (![X35 : $i, X36 : $i, X37 : $i]:
% 17.60/17.87         (~ (r2_hidden @ (k4_tarski @ X35 @ X36) @ X37)
% 17.60/17.87          | (r2_hidden @ X35 @ (k3_relat_1 @ X37))
% 17.60/17.87          | ~ (v1_relat_1 @ X37))),
% 17.60/17.87      inference('cnf', [status(esa)], [t30_relat_1])).
% 17.60/17.87  thf('15', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i]:
% 17.60/17.87         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 17.60/17.87          | ~ (v1_relat_1 @ X0)
% 17.60/17.87          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ (k3_relat_1 @ X0)))),
% 17.60/17.87      inference('sup-', [status(thm)], ['13', '14'])).
% 17.60/17.87  thf('16', plain,
% 17.60/17.87      (![X1 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.60/17.87      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.87  thf('17', plain,
% 17.60/17.87      (![X0 : $i]:
% 17.60/17.87         (~ (v1_relat_1 @ X0)
% 17.60/17.87          | (r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 17.60/17.87          | (r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)))),
% 17.60/17.87      inference('sup-', [status(thm)], ['15', '16'])).
% 17.60/17.87  thf('18', plain,
% 17.60/17.87      (![X0 : $i]:
% 17.60/17.87         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 17.60/17.87          | ~ (v1_relat_1 @ X0))),
% 17.60/17.87      inference('simplify', [status(thm)], ['17'])).
% 17.60/17.87  thf('19', plain,
% 17.60/17.87      (![X13 : $i, X14 : $i]:
% 17.60/17.87         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 17.60/17.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.60/17.87  thf('20', plain,
% 17.60/17.87      (![X0 : $i]:
% 17.60/17.87         (~ (v1_relat_1 @ X0)
% 17.60/17.87          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 17.60/17.87              = (k1_relat_1 @ X0)))),
% 17.60/17.87      inference('sup-', [status(thm)], ['18', '19'])).
% 17.60/17.87  thf('21', plain,
% 17.60/17.87      (![X1 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.60/17.87      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.87  thf(d4_xboole_0, axiom,
% 17.60/17.87    (![A:$i,B:$i,C:$i]:
% 17.60/17.87     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 17.60/17.87       ( ![D:$i]:
% 17.60/17.87         ( ( r2_hidden @ D @ C ) <=>
% 17.60/17.87           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 17.60/17.87  thf('22', plain,
% 17.60/17.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 17.60/17.87         (~ (r2_hidden @ X8 @ X7)
% 17.60/17.87          | (r2_hidden @ X8 @ X6)
% 17.60/17.87          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 17.60/17.87      inference('cnf', [status(esa)], [d4_xboole_0])).
% 17.60/17.87  thf('23', plain,
% 17.60/17.87      (![X5 : $i, X6 : $i, X8 : $i]:
% 17.60/17.87         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 17.60/17.87      inference('simplify', [status(thm)], ['22'])).
% 17.60/17.87  thf('24', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 17.60/17.87          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['21', '23'])).
% 17.60/17.87  thf('25', plain,
% 17.60/17.87      (![X5 : $i, X6 : $i, X8 : $i]:
% 17.60/17.87         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 17.60/17.87      inference('simplify', [status(thm)], ['22'])).
% 17.60/17.87  thf('26', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 17.60/17.87          | (r2_hidden @ 
% 17.60/17.87             (sk_C @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['24', '25'])).
% 17.60/17.87  thf('27', plain,
% 17.60/17.87      (![X1 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.60/17.87      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.87  thf('28', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 17.60/17.87          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['26', '27'])).
% 17.60/17.87  thf('29', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.87         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 17.60/17.87      inference('simplify', [status(thm)], ['28'])).
% 17.60/17.87  thf('30', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 17.60/17.87           (k3_relat_1 @ X0))
% 17.60/17.87          | ~ (v1_relat_1 @ X0))),
% 17.60/17.87      inference('sup+', [status(thm)], ['20', '29'])).
% 17.60/17.87  thf('31', plain,
% 17.60/17.87      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 17.60/17.87        | ~ (v1_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup+', [status(thm)], ['9', '30'])).
% 17.60/17.87  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('33', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('demod', [status(thm)], ['31', '32'])).
% 17.60/17.87  thf('34', plain,
% 17.60/17.87      (![X13 : $i, X14 : $i]:
% 17.60/17.87         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 17.60/17.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.60/17.87  thf('35', plain,
% 17.60/17.87      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 17.60/17.87         = (k1_relat_1 @ sk_A))),
% 17.60/17.87      inference('sup-', [status(thm)], ['33', '34'])).
% 17.60/17.87  thf('36', plain,
% 17.60/17.87      (![X32 : $i]:
% 17.60/17.87         (((k3_relat_1 @ X32)
% 17.60/17.87            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 17.60/17.87          | ~ (v1_relat_1 @ X32))),
% 17.60/17.87      inference('cnf', [status(esa)], [d6_relat_1])).
% 17.60/17.87  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('38', plain,
% 17.60/17.87      (![X33 : $i, X34 : $i]:
% 17.60/17.87         (~ (v1_relat_1 @ X33)
% 17.60/17.87          | (r1_tarski @ (k2_relat_1 @ X34) @ (k2_relat_1 @ X33))
% 17.60/17.87          | ~ (r1_tarski @ X34 @ X33)
% 17.60/17.87          | ~ (v1_relat_1 @ X34))),
% 17.60/17.87      inference('cnf', [status(esa)], [t25_relat_1])).
% 17.60/17.87  thf('39', plain,
% 17.60/17.87      ((~ (v1_relat_1 @ sk_A)
% 17.60/17.87        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 17.60/17.87        | ~ (v1_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup-', [status(thm)], ['37', '38'])).
% 17.60/17.87  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 17.60/17.87      inference('demod', [status(thm)], ['39', '40', '41'])).
% 17.60/17.87  thf(t10_xboole_1, axiom,
% 17.60/17.87    (![A:$i,B:$i,C:$i]:
% 17.60/17.87     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 17.60/17.87  thf('43', plain,
% 17.60/17.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 17.60/17.87         (~ (r1_tarski @ X10 @ X11)
% 17.60/17.87          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 17.60/17.87      inference('cnf', [status(esa)], [t10_xboole_1])).
% 17.60/17.87  thf('44', plain,
% 17.60/17.87      (![X0 : $i]:
% 17.60/17.87         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 17.60/17.87          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 17.60/17.87      inference('sup-', [status(thm)], ['42', '43'])).
% 17.60/17.87  thf('45', plain,
% 17.60/17.87      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 17.60/17.87        | ~ (v1_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup+', [status(thm)], ['36', '44'])).
% 17.60/17.87  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('demod', [status(thm)], ['45', '46'])).
% 17.60/17.87  thf('48', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 17.60/17.87          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['21', '23'])).
% 17.60/17.87  thf('49', plain,
% 17.60/17.87      (![X1 : $i, X3 : $i]:
% 17.60/17.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.60/17.87      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.87  thf('50', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i]:
% 17.60/17.87         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 17.60/17.87          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['48', '49'])).
% 17.60/17.87  thf('51', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.60/17.87      inference('simplify', [status(thm)], ['50'])).
% 17.60/17.87  thf(t8_xboole_1, axiom,
% 17.60/17.87    (![A:$i,B:$i,C:$i]:
% 17.60/17.87     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.60/17.87       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 17.60/17.87  thf('52', plain,
% 17.60/17.87      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.60/17.87         (~ (r1_tarski @ X15 @ X16)
% 17.60/17.87          | ~ (r1_tarski @ X17 @ X16)
% 17.60/17.87          | (r1_tarski @ (k2_xboole_0 @ X15 @ X17) @ X16))),
% 17.60/17.87      inference('cnf', [status(esa)], [t8_xboole_1])).
% 17.60/17.87  thf('53', plain,
% 17.60/17.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.87         ((r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 17.60/17.87          | ~ (r1_tarski @ X2 @ X0))),
% 17.60/17.87      inference('sup-', [status(thm)], ['51', '52'])).
% 17.60/17.87  thf('54', plain,
% 17.60/17.87      (![X0 : $i]:
% 17.60/17.87         (r1_tarski @ 
% 17.60/17.87          (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k3_relat_1 @ sk_B)) @ 
% 17.60/17.87           (k2_relat_1 @ sk_A)) @ 
% 17.60/17.87          (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup-', [status(thm)], ['47', '53'])).
% 17.60/17.87  thf('55', plain,
% 17.60/17.87      ((r1_tarski @ 
% 17.60/17.87        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 17.60/17.87        (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('sup+', [status(thm)], ['35', '54'])).
% 17.60/17.87  thf('56', plain,
% 17.60/17.87      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 17.60/17.87        | ~ (v1_relat_1 @ sk_A))),
% 17.60/17.87      inference('sup+', [status(thm)], ['1', '55'])).
% 17.60/17.87  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 17.60/17.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.87  thf('58', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 17.60/17.87      inference('demod', [status(thm)], ['56', '57'])).
% 17.60/17.87  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 17.60/17.87  
% 17.60/17.87  % SZS output end Refutation
% 17.60/17.87  
% 17.74/17.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
