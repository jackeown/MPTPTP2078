%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0766+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.59hqr2Ouao

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:27 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 130 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  720 (2222 expanded)
%              Number of equality atoms :   23 (  55 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t12_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ? [C: $i] :
                  ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                  & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                    & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                    & ! [D: $i] :
                        ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                          & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                          & ( D != B )
                          & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ? [C: $i] :
                    ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                    & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                      & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                      & ! [D: $i] :
                          ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                            & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                            & ( D != B )
                            & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord1])).

thf('0',plain,(
    r2_hidden @ sk_C_3 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s1_xboole_0__e7_18__wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ? [C: $i] :
        ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
            & ~ ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ X5 @ ( sk_C_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_C_3 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_C_3 @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_C_3 @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_C_3 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ sk_C_3 @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ X7 @ ( k3_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X10: $i] :
      ( ~ ( v2_wellord1 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X10 @ X8 ) @ X10 )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ~ ( v2_wellord1 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X10 @ X8 ) @ X10 )
      | ( X10 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r2_hidden @ X5 @ ( sk_C_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k3_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B @ X16 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_D @ X16 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_D @ X0 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ ( sk_D @ sk_B ) ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_C_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B @ X16 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D @ X16 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( sk_C_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D @ X0 ) ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_wellord1 @ X8 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X10 @ X8 ) @ X9 ) @ X8 )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_wellord1 @ X8 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X10 @ X8 ) @ X9 ) @ X8 )
      | ( X10 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k3_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ X1 @ X0 ) @ X0 ) @ X2 ) @ X0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X6 ) @ X4 )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[s1_xboole_0__e7_18__wellord1])).

thf('47',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( sk_C_1 @ sk_B @ sk_A )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['8','54','55'])).


%------------------------------------------------------------------------------
