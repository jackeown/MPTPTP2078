%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0248+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AwfgKwPyb0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 23.81s
% Output     : Refutation 23.81s
% Verified   : 
% Statistics : Number of formulae       :  209 (1910 expanded)
%              Number of leaves         :   37 ( 608 expanded)
%              Depth                    :   27
%              Number of atoms          : 1584 (20705 expanded)
%              Number of equality atoms :  277 (3775 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ ( B @ C ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ ( B @ C ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X993: $i,X994: $i] :
      ( ( r2_hidden @ ( X993 @ X994 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X993 @ X994 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( X21 @ X19 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ( r2_hidden @ ( X21 @ X18 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( X21 @ X18 ) )
      | ( r2_hidden @ ( X21 @ X20 ) )
      | ~ ( r2_hidden @ ( X21 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X998: $i,X999: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X999 @ X998 ) )
        = X998 )
      | ~ ( r2_hidden @ ( X999 @ X998 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_C_10 ) )
      = sk_C_10 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X998: $i,X999: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X999 @ X998 ) )
        = X998 )
      | ~ ( r2_hidden @ ( X999 @ X998 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('16',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('22',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('25',plain,(
    ! [X192: $i,X193: $i] :
      ( ( k2_xboole_0 @ ( X192 @ ( k3_xboole_0 @ ( X192 @ X193 ) ) ) )
      = X192 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17','18','19','30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_C_10
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( sk_C_10 != sk_C_10 )
      | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
        = sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_C_10 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( sk_B_2
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( ( sk_C_10
       != ( k1_tarski @ sk_A_2 ) )
      & ( sk_B_2
       != ( k1_tarski @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,
    ( ( sk_B_2
      = ( k1_tarski @ sk_A_2 ) )
    | ( sk_C_10
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('46',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['46'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('48',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X20 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('55',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
    | ( ( sk_B_1 @ sk_B_2 )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17','18','19','30','31'])).

thf('60',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_2
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('63',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
        = sk_B_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ ( sk_C_10 @ sk_B_2 ) )
      = sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('70',plain,(
    ! [X1084: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X1084 ) )
      = X1084 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('71',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k3_tarski @ sk_C_10 )
      = sk_A_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k3_tarski @ sk_C_10 )
      = sk_A_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_10 ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('77',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_10 ) )
      = sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ ( B @ C ) ) )
     => ( A = B ) ) )).

thf('79',plain,(
    ! [X1123: $i,X1124: $i,X1125: $i] :
      ( ( X1124 = X1123 )
      | ( ( k1_tarski @ X1124 )
       != ( k2_tarski @ ( X1123 @ X1125 ) ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
       != ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( '#_fresh_sk3' @ sk_C_10 )
      = ( k3_tarski @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['77','81'])).

thf('83',plain,
    ( ( ( '#_fresh_sk3' @ sk_C_10 )
      = sk_A_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['72','82'])).

thf('84',plain,
    ( ( ( ( '#_fresh_sk3' @ sk_C_10 )
        = ( sk_B_1 @ sk_B_2 ) )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['58','83'])).

thf('85',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('86',plain,
    ( ( ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ( sk_B_2 = o_0_0_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( sk_B_2 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('90',plain,(
    ! [X175: $i,X176: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X175 @ X176 ) @ X175 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ ( sk_B_2 @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('93',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('94',plain,
    ( ( ( sk_B_2 = sk_C_10 )
      | ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
    | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['16','17','18','19','30','31'])).

thf('96',plain,
    ( ( sk_B_2
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('97',plain,
    ( ( ( sk_B_2 != sk_C_10 )
      | ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
        = sk_B_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B_2
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('99',plain,
    ( ( sk_B_2 != sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','99'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf('101',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('102',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_10 @ sk_B_2 ) @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_C_10 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
        | ( X0 = sk_A_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( '#_fresh_sk3' @ sk_C_10 )
      = sk_A_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['72','82'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
        | ( X0
          = ( '#_fresh_sk3' @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_C_4 @ ( sk_C_10 @ sk_B_2 ) )
      = ( '#_fresh_sk3' @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ~ ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('110',plain,
    ( ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) )
      | ~ ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','99'])).

thf('112',plain,
    ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_C_10 @ sk_B_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_B_2 = o_0_0_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['87','112'])).

thf('114',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('115',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('116',plain,
    ( ( sk_B_2 != o_0_0_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_B_2
       != ( k1_tarski @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('120',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('121',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('124',plain,
    ( ( sk_C_10 = o_0_0_xboole_0 )
    | ( ( sk_B_1 @ sk_C_10 )
      = sk_A_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('126',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['69','70'])).

thf('127',plain,
    ( ( ( k3_tarski @ sk_B_2 )
      = sk_A_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k3_tarski @ sk_B_2 )
      = sk_A_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('129',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_2 ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('132',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_2 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X1: $i] :
      ( ( '#_fresh_sk3' @ ( k1_tarski @ X1 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['80'])).

thf('134',plain,
    ( ( ( '#_fresh_sk3' @ sk_B_2 )
      = ( k3_tarski @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( '#_fresh_sk3' @ sk_B_2 )
      = sk_A_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['127','134'])).

thf('136',plain,
    ( ( ( ( '#_fresh_sk3' @ sk_B_2 )
        = ( sk_B_1 @ sk_C_10 ) )
      | ( sk_C_10 = o_0_0_xboole_0 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['124','135'])).

thf('137',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('138',plain,
    ( ( ( r2_hidden @ ( '#_fresh_sk3' @ sk_B_2 @ sk_C_10 ) )
      | ( sk_C_10 = o_0_0_xboole_0 )
      | ( sk_C_10 = o_0_0_xboole_0 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( sk_C_10 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( '#_fresh_sk3' @ sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('141',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('142',plain,(
    ! [X363: $i,X364: $i] :
      ( r1_tarski @ ( X363 @ ( k2_xboole_0 @ ( X363 @ X364 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( r1_tarski @ ( sk_C_10 @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('146',plain,
    ( ( ( sk_C_10 = sk_B_2 )
      | ( r2_xboole_0 @ ( sk_C_10 @ sk_B_2 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( sk_C_10
     != ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('148',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('149',plain,
    ( ( sk_C_10 != sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( r2_xboole_0 @ ( sk_C_10 @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('152',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( sk_B_2 @ sk_C_10 ) @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) )
      = sk_B_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_10 ) ) ) )
      | ( X0 = sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( X0 @ sk_B_2 ) )
        | ( X0 = sk_A_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( '#_fresh_sk3' @ sk_B_2 )
      = sk_A_2 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['127','134'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( X0 @ sk_B_2 ) )
        | ( X0
          = ( '#_fresh_sk3' @ sk_B_2 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( sk_C_4 @ ( sk_B_2 @ sk_C_10 ) )
      = ( '#_fresh_sk3' @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ~ ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('160',plain,
    ( ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_B_2 @ sk_C_10 ) )
      | ~ ( r2_xboole_0 @ ( sk_C_10 @ sk_B_2 ) ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r2_xboole_0 @ ( sk_C_10 @ sk_B_2 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['146','149'])).

thf('162',plain,
    ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_B_2 @ sk_C_10 ) )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_C_10 = o_0_0_xboole_0 )
   <= ( sk_C_10
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['139','162'])).

thf('164',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('165',plain,
    ( ( sk_C_10 != k1_xboole_0 )
   <= ( sk_C_10 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('166',plain,
    ( ( sk_C_10 != o_0_0_xboole_0 )
   <= ( sk_C_10 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( sk_C_10
       != ( k1_tarski @ sk_A_2 ) )
      & ( sk_C_10 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,
    ( ( sk_C_10 = k1_xboole_0 )
    | ( sk_C_10
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( sk_C_10 != k1_xboole_0 )
    | ( sk_B_2
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['40'])).

thf('170',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['44','45','47','118','168','169'])).

%------------------------------------------------------------------------------
