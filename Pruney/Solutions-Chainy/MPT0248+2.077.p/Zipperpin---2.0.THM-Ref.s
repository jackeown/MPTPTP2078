%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dzeGOflTOk

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 428 expanded)
%              Number of leaves         :   22 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  826 (4287 expanded)
%              Number of equality atoms :  158 ( 840 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
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
            = ( k2_xboole_0 @ B @ C ) )
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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('41',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','38'])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('55',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('60',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['51','53','61'])).

thf('63',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['48','63'])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('67',plain,
    ( ( ( k5_xboole_0 @ sk_C @ sk_B )
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','39'])).

thf('71',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('78',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','62'])).

thf('84',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['55'])).

thf('86',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['77','86'])).

thf('88',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['76','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','88'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','89'])).

thf('91',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','62'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dzeGOflTOk
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 882 iterations in 0.436s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(t43_zfmisc_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.89          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.89          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.89          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.89        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.70/0.89             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.89             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.70/0.89             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.70/0.89  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(idempotence_k3_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.70/0.89  thf('1', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.70/0.89  thf(t100_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X7 @ X8)
% 0.70/0.89           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf(t92_xboole_1, axiom,
% 0.70/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.89  thf('4', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.89  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf(t36_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.70/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.89  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.70/0.89      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf(t12_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i]:
% 0.70/0.89         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.70/0.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.70/0.89  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t7_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.70/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.89  thf('12', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.70/0.89      inference('sup+', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf(l3_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.70/0.89       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X52 : $i, X53 : $i]:
% 0.70/0.89         (((X53) = (k1_tarski @ X52))
% 0.70/0.89          | ((X53) = (k1_xboole_0))
% 0.70/0.89          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.70/0.89      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.70/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X52 : $i, X53 : $i]:
% 0.70/0.89         (((X53) = (k1_tarski @ X52))
% 0.70/0.89          | ((X53) = (k1_xboole_0))
% 0.70/0.89          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.70/0.89      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.89          | ((sk_B) = (k1_xboole_0))
% 0.70/0.89          | ((X0) = (k1_xboole_0))
% 0.70/0.89          | ((X0) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A))
% 0.70/0.89          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.70/0.89          | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.70/0.89          | ((sk_B) = (k1_xboole_0))
% 0.70/0.89          | ((sk_B) = (k1_xboole_0))
% 0.70/0.89          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['14', '19'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.70/0.89          | ((sk_B) = (k1_xboole_0))
% 0.70/0.89          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['20'])).
% 0.70/0.89  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(t95_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k3_xboole_0 @ A @ B ) =
% 0.70/0.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X22 @ X23)
% 0.70/0.89           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.70/0.89              (k2_xboole_0 @ X22 @ X23)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.70/0.89  thf(t91_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.89       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.70/0.89           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X22 @ X23)
% 0.70/0.89           = (k5_xboole_0 @ X22 @ 
% 0.70/0.89              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.70/0.89      inference('demod', [status(thm)], ['23', '24'])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.70/0.89         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['22', '25'])).
% 0.70/0.89  thf('27', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.70/0.89           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.89  thf(commutativity_k5_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.70/0.89           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.70/0.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['27', '30'])).
% 0.70/0.89  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf(idempotence_k2_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.70/0.89  thf('33', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X22 @ X23)
% 0.70/0.89           = (k5_xboole_0 @ X22 @ 
% 0.70/0.89              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.70/0.89      inference('demod', [status(thm)], ['23', '24'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k3_xboole_0 @ X0 @ X0)
% 0.70/0.89           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('36', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.70/0.89  thf('39', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['32', '38'])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['31', '39'])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      (((k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 0.70/0.89         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['26', '40'])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X7 @ X8)
% 0.70/0.89           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (((k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['31', '39'])).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['43', '44'])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C @ k1_xboole_0))
% 0.70/0.89        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['21', '45'])).
% 0.70/0.89  thf('47', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['32', '38'])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      ((((k1_tarski @ sk_A) = (sk_C))
% 0.70/0.89        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('split', [status(esa)], ['49'])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('split', [status(esa)], ['52'])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('55', plain,
% 0.70/0.89      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['55'])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.70/0.89         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['54', '56'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['57'])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.70/0.89      inference('split', [status(esa)], ['49'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      ((((sk_B) != (sk_B)))
% 0.70/0.89         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['58', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['60'])).
% 0.70/0.89  thf('62', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['51', '53', '61'])).
% 0.70/0.89  thf('63', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['50', '62'])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      ((((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['48', '63'])).
% 0.70/0.89  thf('65', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf('66', plain,
% 0.70/0.89      (((k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      ((((k5_xboole_0 @ sk_C @ sk_B) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['65', '66'])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.70/0.89  thf('69', plain,
% 0.70/0.89      ((((k5_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_B @ sk_C))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['67', '68'])).
% 0.70/0.89  thf('70', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['31', '39'])).
% 0.70/0.89  thf('71', plain,
% 0.70/0.89      ((((sk_C) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['69', '70'])).
% 0.70/0.89  thf('72', plain,
% 0.70/0.89      ((((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['64', '71'])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf('75', plain,
% 0.70/0.89      ((((sk_C) = (k1_xboole_0))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0))
% 0.70/0.89        | ((sk_B) = (k1_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.70/0.89  thf('76', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['75'])).
% 0.70/0.89  thf('77', plain,
% 0.70/0.89      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.70/0.89      inference('split', [status(esa)], ['55'])).
% 0.70/0.89  thf('78', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('79', plain,
% 0.70/0.89      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['57'])).
% 0.70/0.89  thf('80', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('81', plain,
% 0.70/0.89      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.70/0.89         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['79', '80'])).
% 0.70/0.89  thf('82', plain,
% 0.70/0.89      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['78', '81'])).
% 0.70/0.89  thf('83', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['50', '62'])).
% 0.70/0.89  thf('84', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 0.70/0.89  thf('85', plain,
% 0.70/0.89      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.70/0.89      inference('split', [status(esa)], ['55'])).
% 0.70/0.89  thf('86', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.70/0.89  thf('87', plain, (((sk_C) != (k1_xboole_0))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['77', '86'])).
% 0.70/0.89  thf('88', plain, (((sk_B) = (k1_xboole_0))),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['76', '87'])).
% 0.70/0.89  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['9', '88'])).
% 0.70/0.89  thf('90', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['0', '89'])).
% 0.70/0.89  thf('91', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['50', '62'])).
% 0.70/0.89  thf('92', plain, ($false),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
