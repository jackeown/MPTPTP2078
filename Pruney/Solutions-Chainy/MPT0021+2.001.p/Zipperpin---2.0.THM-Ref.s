%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7mvn0xwZMO

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:48 EST 2020

% Result     : Theorem 12.85s
% Output     : Refutation 12.85s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 154 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  653 (1267 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t14_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B )
          & ! [D: $i] :
              ( ( ( r1_tarski @ A @ D )
                & ( r1_tarski @ C @ D ) )
             => ( r1_tarski @ B @ D ) ) )
       => ( B
          = ( k2_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_xboole_1])).

thf('4',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ sk_B @ X16 )
      | ~ ( r1_tarski @ sk_C_1 @ X16 )
      | ~ ( r1_tarski @ sk_A @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['53','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','60','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['10','62'])).

thf('64',plain,(
    sk_B
 != ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7mvn0xwZMO
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:50:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 12.85/13.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.85/13.08  % Solved by: fo/fo7.sh
% 12.85/13.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.85/13.08  % done 9583 iterations in 12.645s
% 12.85/13.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.85/13.08  % SZS output start Refutation
% 12.85/13.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.85/13.08  thf(sk_A_type, type, sk_A: $i).
% 12.85/13.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.85/13.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.85/13.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 12.85/13.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.85/13.08  thf(sk_B_type, type, sk_B: $i).
% 12.85/13.08  thf(commutativity_k2_xboole_0, axiom,
% 12.85/13.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 12.85/13.08  thf('0', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf(t7_xboole_1, axiom,
% 12.85/13.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 12.85/13.08  thf('1', plain,
% 12.85/13.08      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 12.85/13.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.85/13.08  thf('2', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('sup+', [status(thm)], ['0', '1'])).
% 12.85/13.08  thf('3', plain,
% 12.85/13.08      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 12.85/13.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.85/13.08  thf(t14_xboole_1, conjecture,
% 12.85/13.08    (![A:$i,B:$i,C:$i]:
% 12.85/13.08     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 12.85/13.08         ( ![D:$i]:
% 12.85/13.08           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 12.85/13.08             ( r1_tarski @ B @ D ) ) ) ) =>
% 12.85/13.08       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 12.85/13.08  thf(zf_stmt_0, negated_conjecture,
% 12.85/13.08    (~( ![A:$i,B:$i,C:$i]:
% 12.85/13.08        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 12.85/13.08            ( ![D:$i]:
% 12.85/13.08              ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 12.85/13.08                ( r1_tarski @ B @ D ) ) ) ) =>
% 12.85/13.08          ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ) )),
% 12.85/13.08    inference('cnf.neg', [status(esa)], [t14_xboole_1])).
% 12.85/13.08  thf('4', plain,
% 12.85/13.08      (![X16 : $i]:
% 12.85/13.08         ((r1_tarski @ sk_B @ X16)
% 12.85/13.08          | ~ (r1_tarski @ sk_C_1 @ X16)
% 12.85/13.08          | ~ (r1_tarski @ sk_A @ X16))),
% 12.85/13.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.08  thf('5', plain,
% 12.85/13.08      (![X0 : $i]:
% 12.85/13.08         (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0))
% 12.85/13.08          | (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 12.85/13.08      inference('sup-', [status(thm)], ['3', '4'])).
% 12.85/13.08  thf('6', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 12.85/13.08      inference('sup-', [status(thm)], ['2', '5'])).
% 12.85/13.08  thf('7', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('8', plain, ((r1_tarski @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 12.85/13.08      inference('demod', [status(thm)], ['6', '7'])).
% 12.85/13.08  thf(t12_xboole_1, axiom,
% 12.85/13.08    (![A:$i,B:$i]:
% 12.85/13.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 12.85/13.08  thf('9', plain,
% 12.85/13.08      (![X12 : $i, X13 : $i]:
% 12.85/13.08         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 12.85/13.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.85/13.08  thf('10', plain,
% 12.85/13.08      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))
% 12.85/13.08         = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 12.85/13.08      inference('sup-', [status(thm)], ['8', '9'])).
% 12.85/13.08  thf(d3_tarski, axiom,
% 12.85/13.08    (![A:$i,B:$i]:
% 12.85/13.08     ( ( r1_tarski @ A @ B ) <=>
% 12.85/13.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 12.85/13.08  thf('11', plain,
% 12.85/13.08      (![X3 : $i, X5 : $i]:
% 12.85/13.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf(d3_xboole_0, axiom,
% 12.85/13.08    (![A:$i,B:$i,C:$i]:
% 12.85/13.08     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 12.85/13.08       ( ![D:$i]:
% 12.85/13.08         ( ( r2_hidden @ D @ C ) <=>
% 12.85/13.08           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 12.85/13.08  thf('12', plain,
% 12.85/13.08      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 12.85/13.08         (~ (r2_hidden @ X10 @ X8)
% 12.85/13.08          | (r2_hidden @ X10 @ X9)
% 12.85/13.08          | (r2_hidden @ X10 @ X7)
% 12.85/13.08          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 12.85/13.08  thf('13', plain,
% 12.85/13.08      (![X7 : $i, X9 : $i, X10 : $i]:
% 12.85/13.08         ((r2_hidden @ X10 @ X7)
% 12.85/13.08          | (r2_hidden @ X10 @ X9)
% 12.85/13.08          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X9 @ X7)))),
% 12.85/13.08      inference('simplify', [status(thm)], ['12'])).
% 12.85/13.08  thf('14', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 12.85/13.08      inference('sup-', [status(thm)], ['11', '13'])).
% 12.85/13.08  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 12.85/13.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.08  thf('16', plain,
% 12.85/13.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.85/13.08         (~ (r2_hidden @ X2 @ X3)
% 12.85/13.08          | (r2_hidden @ X2 @ X4)
% 12.85/13.08          | ~ (r1_tarski @ X3 @ X4))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('17', plain,
% 12.85/13.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 12.85/13.08      inference('sup-', [status(thm)], ['15', '16'])).
% 12.85/13.08  thf('18', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ X0)
% 12.85/13.08          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ X1)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 12.85/13.08      inference('sup-', [status(thm)], ['14', '17'])).
% 12.85/13.08  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 12.85/13.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.08  thf('20', plain,
% 12.85/13.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.85/13.08         (~ (r2_hidden @ X2 @ X3)
% 12.85/13.08          | (r2_hidden @ X2 @ X4)
% 12.85/13.08          | ~ (r1_tarski @ X3 @ X4))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('21', plain,
% 12.85/13.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 12.85/13.08      inference('sup-', [status(thm)], ['19', '20'])).
% 12.85/13.08  thf('22', plain,
% 12.85/13.08      (![X0 : $i]:
% 12.85/13.08         ((r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ sk_C_1)) @ sk_B)
% 12.85/13.08          | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 12.85/13.08      inference('sup-', [status(thm)], ['18', '21'])).
% 12.85/13.08  thf('23', plain,
% 12.85/13.08      (![X0 : $i]:
% 12.85/13.08         ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ sk_A @ sk_C_1)) @ sk_B))),
% 12.85/13.08      inference('simplify', [status(thm)], ['22'])).
% 12.85/13.08  thf('24', plain,
% 12.85/13.08      (![X3 : $i, X5 : $i]:
% 12.85/13.08         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('25', plain,
% 12.85/13.08      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)
% 12.85/13.08        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 12.85/13.08      inference('sup-', [status(thm)], ['23', '24'])).
% 12.85/13.08  thf('26', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 12.85/13.08      inference('simplify', [status(thm)], ['25'])).
% 12.85/13.08  thf('27', plain,
% 12.85/13.08      (![X12 : $i, X13 : $i]:
% 12.85/13.08         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 12.85/13.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.85/13.08  thf('28', plain,
% 12.85/13.08      (((k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B) = (sk_B))),
% 12.85/13.08      inference('sup-', [status(thm)], ['26', '27'])).
% 12.85/13.08  thf('29', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('30', plain,
% 12.85/13.08      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 12.85/13.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.85/13.08  thf('31', plain,
% 12.85/13.08      (![X12 : $i, X13 : $i]:
% 12.85/13.08         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 12.85/13.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.85/13.08  thf('32', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('sup-', [status(thm)], ['30', '31'])).
% 12.85/13.08  thf('33', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('sup+', [status(thm)], ['29', '32'])).
% 12.85/13.08  thf('34', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('sup+', [status(thm)], ['29', '32'])).
% 12.85/13.08  thf('35', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 12.85/13.08      inference('sup+', [status(thm)], ['33', '34'])).
% 12.85/13.08  thf('36', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('37', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('sup+', [status(thm)], ['29', '32'])).
% 12.85/13.08  thf('38', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('demod', [status(thm)], ['35', '36', '37'])).
% 12.85/13.08  thf('39', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('40', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 12.85/13.08           = (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('sup+', [status(thm)], ['38', '39'])).
% 12.85/13.08  thf('41', plain,
% 12.85/13.08      (![X3 : $i, X5 : $i]:
% 12.85/13.08         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('42', plain,
% 12.85/13.08      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 12.85/13.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.85/13.08  thf('43', plain,
% 12.85/13.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 12.85/13.08         (~ (r2_hidden @ X2 @ X3)
% 12.85/13.08          | (r2_hidden @ X2 @ X4)
% 12.85/13.08          | ~ (r1_tarski @ X3 @ X4))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('44', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 12.85/13.08      inference('sup-', [status(thm)], ['42', '43'])).
% 12.85/13.08  thf('45', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((r1_tarski @ X0 @ X1)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 12.85/13.08      inference('sup-', [status(thm)], ['41', '44'])).
% 12.85/13.08  thf('46', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 12.85/13.08      inference('sup-', [status(thm)], ['42', '43'])).
% 12.85/13.08  thf('47', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.85/13.08         ((r1_tarski @ X1 @ X2)
% 12.85/13.08          | (r2_hidden @ (sk_C @ X2 @ X1) @ 
% 12.85/13.08             (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)))),
% 12.85/13.08      inference('sup-', [status(thm)], ['45', '46'])).
% 12.85/13.08  thf('48', plain,
% 12.85/13.08      (![X3 : $i, X5 : $i]:
% 12.85/13.08         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 12.85/13.08      inference('cnf', [status(esa)], [d3_tarski])).
% 12.85/13.08  thf('49', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 12.85/13.08          | (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 12.85/13.08      inference('sup-', [status(thm)], ['47', '48'])).
% 12.85/13.08  thf('50', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 12.85/13.08      inference('simplify', [status(thm)], ['49'])).
% 12.85/13.08  thf('51', plain,
% 12.85/13.08      (![X12 : $i, X13 : $i]:
% 12.85/13.08         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 12.85/13.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.85/13.08  thf('52', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 12.85/13.08           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 12.85/13.08      inference('sup-', [status(thm)], ['50', '51'])).
% 12.85/13.08  thf('53', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 12.85/13.08           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 12.85/13.08           = (k2_xboole_0 @ 
% 12.85/13.08              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)) @ 
% 12.85/13.08              X2))),
% 12.85/13.08      inference('sup+', [status(thm)], ['40', '52'])).
% 12.85/13.08  thf('54', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('55', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('sup+', [status(thm)], ['0', '1'])).
% 12.85/13.08  thf('56', plain,
% 12.85/13.08      (![X12 : $i, X13 : $i]:
% 12.85/13.08         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 12.85/13.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.85/13.08  thf('57', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('sup-', [status(thm)], ['55', '56'])).
% 12.85/13.08  thf('58', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('sup+', [status(thm)], ['54', '57'])).
% 12.85/13.08  thf('59', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ X1 @ X0))),
% 12.85/13.08      inference('demod', [status(thm)], ['35', '36', '37'])).
% 12.85/13.08  thf('60', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.08         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 12.85/13.08           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2))),
% 12.85/13.08      inference('demod', [status(thm)], ['53', '58', '59'])).
% 12.85/13.08  thf('61', plain,
% 12.85/13.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.85/13.08      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.85/13.08  thf('62', plain,
% 12.85/13.08      (((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1)) = (sk_B))),
% 12.85/13.08      inference('demod', [status(thm)], ['28', '60', '61'])).
% 12.85/13.08  thf('63', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_B))),
% 12.85/13.08      inference('sup+', [status(thm)], ['10', '62'])).
% 12.85/13.08  thf('64', plain, (((sk_B) != (k2_xboole_0 @ sk_A @ sk_C_1))),
% 12.85/13.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.08  thf('65', plain, ($false),
% 12.85/13.08      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 12.85/13.08  
% 12.85/13.08  % SZS output end Refutation
% 12.85/13.08  
% 12.85/13.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
