%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0247+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rEZL2BOklW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 27.26s
% Output     : Refutation 27.26s
% Verified   : 
% Statistics : Number of formulae       :  212 (18486 expanded)
%              Number of leaves         :   31 (4361 expanded)
%              Depth                    :   45
%              Number of atoms          : 1810 (233598 expanded)
%              Number of equality atoms :  314 (41604 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('0',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t42_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k2_tarski @ ( B @ C ) ) ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ ( k2_tarski @ ( B @ C ) ) ) )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_zfmisc_1])).

thf('1',plain,
    ( ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = k1_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('5',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ ( k1_tarski @ B ) ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1021: $i,X1022: $i] :
      ( ( X1022
        = ( k1_tarski @ X1021 ) )
      | ( X1022 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X1022 @ ( k1_tarski @ X1021 ) ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X1021: $i,X1022: $i] :
      ( ( X1022
        = ( k1_tarski @ X1021 ) )
      | ( X1022 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X1022 @ ( k1_tarski @ X1021 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
        | ( X0 = o_0_0_xboole_0 )
        | ( X0
          = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
        | ( X0 = o_0_0_xboole_0 )
        | ( X0 = sk_A_2 ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = k1_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,
    ( ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A_2 != k1_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,
    ( ( sk_A_2 != o_0_0_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('21',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,
    ( ( sk_A_2 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('26',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
      & ( sk_A_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
    | ( sk_A_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','29'])).

thf('31',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','30'])).

thf('32',plain,
    ( ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('34',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
    | ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k2_tarski @ ( B @ C ) ) ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ ( B @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X1026: $i,X1027: $i,X1028: $i] :
      ( ( X1028
        = ( k2_tarski @ ( X1026 @ X1027 ) ) )
      | ( X1028
        = ( k1_tarski @ X1027 ) )
      | ( X1028
        = ( k1_tarski @ X1026 ) )
      | ( X1028 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X1028 @ ( k2_tarski @ ( X1026 @ X1027 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X1026: $i,X1027: $i,X1028: $i] :
      ( ( X1028
        = ( k2_tarski @ ( X1026 @ X1027 ) ) )
      | ( X1028
        = ( k1_tarski @ X1027 ) )
      | ( X1028
        = ( k1_tarski @ X1026 ) )
      | ( X1028 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X1028 @ ( k2_tarski @ ( X1026 @ X1027 ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( sk_A_2 = o_0_0_xboole_0 )
      | ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) )
      | ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) )
      | ( sk_A_2
        = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','30'])).

thf('46',plain,
    ( ( ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) )
      | ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) )
      | ( sk_A_2
        = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('48',plain,
    ( ( ( sk_A_2 != sk_A_2 )
      | ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) )
      | ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) ) )
   <= ( ( sk_A_2
       != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
      & ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) )
      | ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) ) )
   <= ( ( sk_A_2
       != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
      & ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,
    ( ( ( sk_A_2 != sk_A_2 )
      | ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) ) )
   <= ( ( sk_A_2
       != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
      & ( sk_A_2
       != ( k1_tarski @ sk_C_10 ) )
      & ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( ( sk_A_2
       != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
      & ( sk_A_2
       != ( k1_tarski @ sk_C_10 ) )
      & ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('54',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( sk_A_2
       != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
      & ( sk_A_2
       != ( k1_tarski @ sk_C_10 ) )
      & ( sk_A_2
       != ( k1_tarski @ sk_B_2 ) )
      & ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','37','39','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['33','56'])).

thf('58',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) )
    | ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference('sup-',[status(thm)],['32','57'])).

thf('59',plain,
    ( ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( X0 @ X0 ) )
      | ( r1_tarski @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_A_2
      = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('66',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_A_2 ) )
   <= ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
      & ( sk_A_2
        = ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A_2
     != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A_2
 != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference('sat_resolution*',[status(thm)],['35','37','39','55','67'])).

thf('69',plain,(
    sk_A_2
 != ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(simpl_trail,[status(thm)],['59','68'])).

thf('70',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['36'])).

thf('72',plain,
    ( ( ( sk_A_2 != sk_A_2 )
      | ( sk_A_2
        = ( k1_tarski @ sk_B_2 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ ( A @ B ) ) ) )).

thf('74',plain,(
    ! [X1011: $i,X1013: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1011 @ X1013 ) )
        = ( k1_tarski @ X1011 ) )
      | ( r2_hidden @ ( X1011 @ X1013 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
          = ( k1_tarski @ sk_B_2 ) )
        | ( r2_hidden @ ( sk_B_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
          = sk_A_2 )
        | ( r2_hidden @ ( sk_B_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('79',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('80',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('82',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('83',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('84',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ ( B @ C ) ) )
     => ( A = B ) ) )).

thf('85',plain,(
    ! [X1119: $i,X1120: $i,X1121: $i] :
      ( ( X1120 = X1119 )
      | ( ( k1_tarski @ X1120 )
       != ( k2_tarski @ ( X1119 @ X1121 ) ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
       != ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['83','87'])).

thf('89',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['80','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
          = sk_A_2 )
        | ( r2_hidden @ ( '#_fresh_sk3' @ sk_A_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['77','89'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('91',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
          = sk_A_2 )
        | ( r1_tarski @ ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

thf('94',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('95',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('97',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

thf('99',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('101',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

thf('103',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('104',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('106',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
    | ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('108',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('109',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
    | ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
    | ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('113',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('114',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('116',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf('119',plain,
    ( ( '#_fresh_sk3' @ sk_A_2 )
    = ( k3_tarski @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['101','119'])).

thf('121',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('123',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('124',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_C_10 )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','69'])).

thf('127',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) )
    | ( sk_A_2
      = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ) ),
    inference('sup+',[status(thm)],['121','128'])).

thf('130',plain,
    ( sk_A_2
    = ( k1_tarski @ ( '#_fresh_sk3' @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
          = sk_A_2 )
        | ( r1_tarski @ ( sk_A_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['92','130'])).

thf('132',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['33','56'])).

thf('133',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
      = sk_A_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['80','88'])).

thf('135',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ sk_C_10 ) ) ) )
      = sk_A_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('136',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X444 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('137',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X444 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('139',plain,(
    ! [X1011: $i,X1012: $i] :
      ( ~ ( r2_hidden @ ( X1011 @ X1012 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1011 @ X1012 ) )
       != ( k1_tarski @ X1011 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
         != ( k1_tarski @ sk_B_2 ) )
        | ~ ( r2_hidden @ ( sk_B_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
         != sk_A_2 )
        | ~ ( r2_hidden @ ( sk_B_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = sk_B_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['80','88'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
         != sk_A_2 )
        | ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_A_2 @ X0 ) ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ X0 ) ) ) )
       != sk_A_2 )
   <= ( sk_A_2
     != ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,
    ( sk_A_2
    = ( k1_tarski @ sk_C_10 ) ),
    inference('simplify_reflect-',[status(thm)],['135','145'])).

thf('147',plain,
    ( sk_A_2
    = ( k1_tarski @ sk_C_10 ) ),
    inference('sat_resolution*',[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( X0 = sk_A_2 ) ) ),
    inference(simpl_trail,[status(thm)],['12','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
        = sk_A_2 )
      | ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','148'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('150',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
      | ( ( k4_xboole_0 @ ( sk_A_2 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('152',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('153',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('154',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_A_2 @ X0 ) )
      | ( r1_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k3_tarski @ sk_A_2 )
      = sk_C_10 )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('158',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('159',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ ( k3_tarski @ sk_A_2 ) ) ) ) )
   <= ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
      & ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('161',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('162',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('163',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('164',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ sk_B_2 ) ) ) )
   <= ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) )
      & ( sk_A_2
        = ( k1_tarski @ sk_C_10 ) ) ) ),
    inference(demod,[status(thm)],['159','162','163'])).

thf('165',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_C_10 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','37','39','55'])).

thf('166',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ sk_B_2 ) ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(simpl_trail,[status(thm)],['164','165'])).

thf('167',plain,
    ( sk_A_2
    = ( k1_tarski @ sk_C_10 ) ),
    inference('sat_resolution*',[status(thm)],['146'])).

thf('168',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['166','167'])).

thf('169',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['156','168'])).

thf('170',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X444 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('171',plain,
    ( ( sk_A_2
      = ( k1_tarski @ ( k3_tarski @ sk_A_2 ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A @ B ) )
        & ( r2_hidden @ ( A @ B ) ) ) )).

thf('172',plain,(
    ! [X1000: $i,X1001: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1000 @ X1001 ) )
      | ~ ( r2_hidden @ ( X1000 @ X1001 ) ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
        | ~ ( r2_hidden @ ( k3_tarski @ sk_A_2 @ X0 ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ! [X0: $i] :
        ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( k3_tarski @ sk_A_2 @ X0 ) ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,
    ( ( ( '#_fresh_sk3' @ sk_A_2 )
      = ( k3_tarski @ sk_A_2 ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('176',plain,
    ( ! [X0: $i] :
        ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ X0 ) ) ) )
   <= ( sk_A_2
      = ( k1_tarski @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( sk_A_2
    = ( k1_tarski @ sk_C_10 ) ),
    inference('sat_resolution*',[status(thm)],['146'])).

thf('178',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k2_tarski @ ( '#_fresh_sk3' @ sk_A_2 @ X0 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('179',plain,(
    $false ),
    inference('sup-',[status(thm)],['169','178'])).

%------------------------------------------------------------------------------
