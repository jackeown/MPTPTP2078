%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0735+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wlb2mIk9xS

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:25 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 291 expanded)
%              Number of leaves         :   19 (  94 expanded)
%              Depth                    :   25
%              Number of atoms          :  719 (2268 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf(t23_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ( ( r2_hidden @ A @ B )
         => ( v3_ordinal1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_ordinal1])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,
    ( ~ ( v1_ordinal1 @ sk_B_2 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v3_ordinal1 @ sk_B_2 )
    | ( r1_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v2_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( r2_hidden @ ( sk_B_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X9 = X7 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v2_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_ordinal1 @ sk_A )
      | ~ ( v2_ordinal1 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ( X0
        = ( sk_B_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_B_2 )
      | ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( X0
        = ( sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v2_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ( X0
        = ( sk_B_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v2_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A ) @ ( sk_B_1 @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 ) @ ( sk_B_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('23',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ( ( sk_B_1 @ X10 )
       != ( sk_C @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('26',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( v2_ordinal1 @ X10 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X10 ) @ ( sk_C @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('28',plain,(
    v2_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( ( v3_ordinal1 @ X3 )
      | ~ ( v2_ordinal1 @ X3 )
      | ~ ( v1_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_ordinal1])).

thf('30',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('38',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('40',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ~ ( v1_ordinal1 @ sk_B_2 )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v3_ordinal1 @ sk_B_2 )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_2 )
    | ( v1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_2 )
    | ( v1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( sk_B @ sk_A ) ) @ sk_B_2 )
      | ( v1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v2_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X9 = X7 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v2_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_ordinal1 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ sk_B_2 )
      | ( r2_hidden @ X0 @ sk_A )
      | ( X0 = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ( X0 = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_ordinal1 @ sk_A )
      | ( r1_tarski @ ( sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ ( sk_C_1 @ X0 @ ( sk_B @ sk_A ) ) )
      | ( ( sk_C_1 @ X0 @ ( sk_B @ sk_A ) )
        = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X14 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X14 @ X12 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,
    ( ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = sk_A )
    | ( r2_hidden @ sk_A @ ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) ) )
    | ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf(t3_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ A ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_ordinal1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ X1 @ ( sk_B @ X0 ) ) )
      | ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('66',plain,
    ( ( ( sk_C_1 @ sk_A @ ( sk_B @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','71'])).

thf('73',plain,(
    ~ ( v1_ordinal1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('74',plain,(
    r1_tarski @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( r1_tarski @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('76',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['32','76'])).


%------------------------------------------------------------------------------
