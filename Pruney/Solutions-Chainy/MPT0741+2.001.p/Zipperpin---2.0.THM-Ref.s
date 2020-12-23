%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AoGUmXrbWs

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 372 expanded)
%              Number of leaves         :   21 ( 118 expanded)
%              Depth                    :   36
%              Number of atoms          :  722 (2674 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v3_ordinal1 @ X1 )
      | ~ ( v2_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_ordinal1])).

thf(t31_ordinal1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( v3_ordinal1 @ B )
            & ( r1_tarski @ B @ A ) ) )
     => ( v3_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( ( v3_ordinal1 @ B )
              & ( r1_tarski @ B @ A ) ) )
       => ( v3_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t31_ordinal1])).

thf('1',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,(
    ! [X23: $i] :
      ( ( r1_tarski @ X23 @ sk_A )
      | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ~ ( r1_tarski @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,(
    v1_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_ordinal1 @ X14 ) )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('11',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X22 ) )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('13',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( v3_ordinal1 @ X23 )
      | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('18',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r1_ordinal1 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v1_ordinal1 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('25',plain,(
    v1_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( r1_tarski @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( r1_tarski @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B_1 @ sk_A ) @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t22_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v1_ordinal1 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ( ( sk_B_1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X9 ) @ ( sk_C @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('48',plain,
    ( ( ( sk_B_1 @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('50',plain,(
    ! [X23: $i] :
      ( ( v3_ordinal1 @ X23 )
      | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('53',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_B_1 @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( ( sk_B_1 @ X9 )
       != ( sk_C @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('56',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('58',plain,(
    r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('60',plain,
    ( ( r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('62',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('63',plain,(
    r1_tarski @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t22_ordinal1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ ( sk_C @ sk_A ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('68',plain,(
    v1_ordinal1 @ ( sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A ) @ ( k1_ordinal1 @ ( sk_B_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','70'])).

thf('72',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ ( k1_ordinal1 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','71'])).

thf('73',plain,(
    v3_ordinal1 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('74',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ ( k1_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ~ ( r2_hidden @ ( sk_C @ X9 ) @ ( sk_B_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('78',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( ( sk_B_1 @ X9 )
       != ( sk_C @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('80',plain,(
    v2_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['8','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AoGUmXrbWs
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:00:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 233 iterations in 0.145s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.36/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.36/0.59  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.36/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.59  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i > $i).
% 0.36/0.59  thf(cc2_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) => ( v3_ordinal1 @ A ) ))).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (![X1 : $i]:
% 0.36/0.59         ((v3_ordinal1 @ X1) | ~ (v2_ordinal1 @ X1) | ~ (v1_ordinal1 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc2_ordinal1])).
% 0.36/0.59  thf(t31_ordinal1, conjecture,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ![B:$i]:
% 0.36/0.59         ( ( r2_hidden @ B @ A ) =>
% 0.36/0.59           ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.36/0.59       ( v3_ordinal1 @ A ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i]:
% 0.36/0.59        ( ( ![B:$i]:
% 0.36/0.59            ( ( r2_hidden @ B @ A ) =>
% 0.36/0.59              ( ( v3_ordinal1 @ B ) & ( r1_tarski @ B @ A ) ) ) ) =>
% 0.36/0.59          ( v3_ordinal1 @ A ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t31_ordinal1])).
% 0.36/0.59  thf('1', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('2', plain, ((~ (v1_ordinal1 @ sk_A) | ~ (v2_ordinal1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.59  thf(d2_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v1_ordinal1 @ A ) <=>
% 0.36/0.59       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X5 : $i]: ((v1_ordinal1 @ X5) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X23 : $i]: ((r1_tarski @ X23 @ sk_A) | ~ (r2_hidden @ X23 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (((v1_ordinal1 @ sk_A) | (r1_tarski @ (sk_B @ sk_A) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X5 : $i]: ((v1_ordinal1 @ X5) | ~ (r1_tarski @ (sk_B @ X5) @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.36/0.59  thf('7', plain, ((v1_ordinal1 @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf('8', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.59  thf(t29_ordinal1, axiom,
% 0.36/0.59    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (![X22 : $i]:
% 0.36/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.36/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.36/0.59  thf(t13_ordinal1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.59       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i]:
% 0.36/0.59         ((r2_hidden @ X13 @ (k1_ordinal1 @ X14)) | ((X13) != (X14)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.59  thf('11', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.36/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X22 : $i]:
% 0.36/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X22)) | ~ (v3_ordinal1 @ X22))),
% 0.36/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.36/0.59  thf('13', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.36/0.59      inference('simplify', [status(thm)], ['10'])).
% 0.36/0.59  thf(d3_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v2_ordinal1 @ A ) <=>
% 0.36/0.59       ( ![B:$i,C:$i]:
% 0.36/0.59         ( ~( ( r2_hidden @ B @ A ) & ( r2_hidden @ C @ A ) & 
% 0.36/0.59              ( ~( r2_hidden @ B @ C ) ) & ( ( B ) != ( C ) ) & 
% 0.36/0.59              ( ~( r2_hidden @ C @ B ) ) ) ) ) ))).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X9 : $i]: ((v2_ordinal1 @ X9) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X23 : $i]: ((v3_ordinal1 @ X23) | ~ (r2_hidden @ X23 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('16', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.59  thf('17', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.59  thf('18', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(t26_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X20 : $i, X21 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X20)
% 0.36/0.59          | (r1_ordinal1 @ X21 @ X20)
% 0.36/0.59          | (r2_hidden @ X20 @ X21)
% 0.36/0.59          | ~ (v3_ordinal1 @ X21))),
% 0.36/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X3 : $i, X4 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X3 @ X4)
% 0.36/0.59          | (r1_tarski @ X3 @ X4)
% 0.36/0.59          | ~ (v1_ordinal1 @ X4))),
% 0.36/0.59      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.36/0.59          | ~ (v3_ordinal1 @ X1)
% 0.36/0.59          | ~ (v1_ordinal1 @ X0)
% 0.36/0.59          | (r1_tarski @ X1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v1_ordinal1 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['18', '21'])).
% 0.36/0.59  thf('23', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(cc1_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.36/0.59  thf('24', plain, (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.36/0.59  thf('25', plain, ((v1_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['22', '25'])).
% 0.36/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.36/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X10)
% 0.36/0.59          | ~ (v3_ordinal1 @ X11)
% 0.36/0.59          | (r1_ordinal1 @ X10 @ X11)
% 0.36/0.59          | ~ (r1_tarski @ X10 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_ordinal1 @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.59  thf('29', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_ordinal1 @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ (sk_B_1 @ sk_A) @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X10)
% 0.36/0.59          | ~ (v3_ordinal1 @ X11)
% 0.36/0.59          | (r1_tarski @ X10 @ X11)
% 0.36/0.59          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | (r1_tarski @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.59  thf('34', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | (r1_tarski @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.59  thf(t22_ordinal1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v1_ordinal1 @ A ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.59           ( ![C:$i]:
% 0.36/0.59             ( ( v3_ordinal1 @ C ) =>
% 0.36/0.59               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.36/0.59                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X15)
% 0.36/0.59          | ~ (r1_tarski @ X16 @ X15)
% 0.36/0.59          | ~ (r2_hidden @ X15 @ X17)
% 0.36/0.59          | (r2_hidden @ X16 @ X17)
% 0.36/0.59          | ~ (v3_ordinal1 @ X17)
% 0.36/0.59          | ~ (v1_ordinal1 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v1_ordinal1 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X1)
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ X1)
% 0.36/0.59          | ~ (r2_hidden @ X0 @ X1)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.59  thf('39', plain, ((v1_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X1)
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ X1)
% 0.36/0.59          | ~ (r2_hidden @ X0 @ X1)
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ X1)
% 0.36/0.59          | ~ (v3_ordinal1 @ X1)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ (k1_ordinal1 @ X0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['13', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ (k1_ordinal1 @ X0))
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '42'])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ (k1_ordinal1 @ X0))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         (((X13) = (X12))
% 0.36/0.59          | (r2_hidden @ X13 @ X12)
% 0.36/0.59          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r1_ordinal1 @ X0 @ (sk_B_1 @ sk_A))
% 0.36/0.59          | (r2_hidden @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ((sk_B_1 @ sk_A) = (X0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (![X9 : $i]:
% 0.36/0.59         ((v2_ordinal1 @ X9) | ~ (r2_hidden @ (sk_B_1 @ X9) @ (sk_C @ X9)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      ((((sk_B_1 @ sk_A) = (sk_C @ sk_A))
% 0.36/0.59        | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.36/0.59        | (v2_ordinal1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (![X9 : $i]: ((v2_ordinal1 @ X9) | (r2_hidden @ (sk_C @ X9) @ X9))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('50', plain,
% 0.36/0.59      (![X23 : $i]: ((v3_ordinal1 @ X23) | ~ (r2_hidden @ X23 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('51', plain, (((v2_ordinal1 @ sk_A) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf('52', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.59  thf('53', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('54', plain,
% 0.36/0.59      ((((sk_B_1 @ sk_A) = (sk_C @ sk_A))
% 0.36/0.59        | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.36/0.59        | (v2_ordinal1 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['48', '53'])).
% 0.36/0.59  thf('55', plain,
% 0.36/0.59      (![X9 : $i]: ((v2_ordinal1 @ X9) | ((sk_B_1 @ X9) != (sk_C @ X9)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (((v2_ordinal1 @ sk_A) | (r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('clc', [status(thm)], ['54', '55'])).
% 0.36/0.59  thf('57', plain, (~ (v2_ordinal1 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.59  thf('58', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['56', '57'])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X10)
% 0.36/0.59          | ~ (v3_ordinal1 @ X11)
% 0.36/0.59          | (r1_tarski @ X10 @ X11)
% 0.36/0.59          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.36/0.59  thf('60', plain,
% 0.36/0.59      (((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.36/0.59        | ~ (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.59  thf('61', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('62', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('63', plain, ((r1_tarski @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X15)
% 0.36/0.59          | ~ (r1_tarski @ X16 @ X15)
% 0.36/0.59          | ~ (r2_hidden @ X15 @ X17)
% 0.36/0.59          | (r2_hidden @ X16 @ X17)
% 0.36/0.59          | ~ (v3_ordinal1 @ X17)
% 0.36/0.59          | ~ (v1_ordinal1 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t22_ordinal1])).
% 0.36/0.59  thf('65', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_ordinal1 @ (sk_C @ sk_A))
% 0.36/0.59          | ~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_C @ sk_A) @ X0)
% 0.36/0.59          | ~ (r2_hidden @ (sk_B_1 @ sk_A) @ X0)
% 0.36/0.59          | ~ (v3_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.59  thf('66', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('67', plain, (![X0 : $i]: ((v1_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.36/0.59  thf('68', plain, ((v1_ordinal1 @ (sk_C @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.59  thf('69', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('70', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v3_ordinal1 @ X0)
% 0.36/0.59          | (r2_hidden @ (sk_C @ sk_A) @ X0)
% 0.36/0.59          | ~ (r2_hidden @ (sk_B_1 @ sk_A) @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['65', '68', '69'])).
% 0.36/0.59  thf('71', plain,
% 0.36/0.59      (((r2_hidden @ (sk_C @ sk_A) @ (k1_ordinal1 @ (sk_B_1 @ sk_A)))
% 0.36/0.59        | ~ (v3_ordinal1 @ (k1_ordinal1 @ (sk_B_1 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['11', '70'])).
% 0.36/0.59  thf('72', plain,
% 0.36/0.59      ((~ (v3_ordinal1 @ (sk_B_1 @ sk_A))
% 0.36/0.59        | (r2_hidden @ (sk_C @ sk_A) @ (k1_ordinal1 @ (sk_B_1 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['9', '71'])).
% 0.36/0.59  thf('73', plain, ((v3_ordinal1 @ (sk_B_1 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('74', plain,
% 0.36/0.59      ((r2_hidden @ (sk_C @ sk_A) @ (k1_ordinal1 @ (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['72', '73'])).
% 0.36/0.59  thf('75', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i]:
% 0.36/0.59         (((X13) = (X12))
% 0.36/0.59          | (r2_hidden @ X13 @ X12)
% 0.36/0.59          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.36/0.59  thf('76', plain,
% 0.36/0.59      (((r2_hidden @ (sk_C @ sk_A) @ (sk_B_1 @ sk_A))
% 0.36/0.59        | ((sk_C @ sk_A) = (sk_B_1 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.59  thf('77', plain,
% 0.36/0.59      (![X9 : $i]:
% 0.36/0.59         ((v2_ordinal1 @ X9) | ~ (r2_hidden @ (sk_C @ X9) @ (sk_B_1 @ X9)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('78', plain,
% 0.36/0.59      ((((sk_C @ sk_A) = (sk_B_1 @ sk_A)) | (v2_ordinal1 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.36/0.59  thf('79', plain,
% 0.36/0.59      (![X9 : $i]: ((v2_ordinal1 @ X9) | ((sk_B_1 @ X9) != (sk_C @ X9)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_ordinal1])).
% 0.36/0.59  thf('80', plain, ((v2_ordinal1 @ sk_A)),
% 0.36/0.59      inference('clc', [status(thm)], ['78', '79'])).
% 0.36/0.59  thf('81', plain, ($false), inference('demod', [status(thm)], ['8', '80'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
