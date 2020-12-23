%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgbfbT0znU

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 261 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  702 (2966 expanded)
%              Number of equality atoms :  121 ( 640 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('10',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X58
        = ( k1_tarski @ X57 ) )
      | ( X58 = k1_xboole_0 )
      | ~ ( r1_tarski @ X58 @ ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','11','23'])).

thf('25',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','46'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('52',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X55 ) @ X56 )
      | ( r2_hidden @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('54',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X52 ) @ X54 )
      | ~ ( r2_hidden @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','59'])).

thf('61',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','24'])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','25'])).

thf('72',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('74',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['67','74'])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['66','75'])).

thf('77',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['27','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['26','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgbfbT0znU
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:28:41 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.25/1.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.25/1.44  % Solved by: fo/fo7.sh
% 1.25/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.25/1.44  % done 2458 iterations in 0.953s
% 1.25/1.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.25/1.44  % SZS output start Refutation
% 1.25/1.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.25/1.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.25/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.25/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.25/1.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.25/1.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.25/1.44  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.25/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.25/1.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.25/1.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.25/1.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.25/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.25/1.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.25/1.44  thf(t43_zfmisc_1, conjecture,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.25/1.44          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.25/1.44          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.25/1.44          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.25/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.25/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.25/1.44        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.25/1.44             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.25/1.44             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.25/1.44             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.25/1.44    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.25/1.44  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(d3_tarski, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( r1_tarski @ A @ B ) <=>
% 1.25/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.25/1.44  thf('1', plain,
% 1.25/1.44      (![X6 : $i, X8 : $i]:
% 1.25/1.44         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 1.25/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.25/1.44  thf(d1_xboole_0, axiom,
% 1.25/1.44    (![A:$i]:
% 1.25/1.44     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.25/1.44  thf('2', plain,
% 1.25/1.44      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 1.25/1.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.25/1.44  thf('3', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.25/1.44      inference('sup-', [status(thm)], ['1', '2'])).
% 1.25/1.44  thf(t12_xboole_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.25/1.44  thf('4', plain,
% 1.25/1.44      (![X14 : $i, X15 : $i]:
% 1.25/1.44         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 1.25/1.44      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.25/1.44  thf('5', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['3', '4'])).
% 1.25/1.44  thf('6', plain,
% 1.25/1.44      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.25/1.44      inference('sup+', [status(thm)], ['0', '5'])).
% 1.25/1.44  thf('7', plain,
% 1.25/1.44      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('8', plain,
% 1.25/1.44      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.25/1.44         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('split', [status(esa)], ['7'])).
% 1.25/1.44  thf('9', plain,
% 1.25/1.44      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('split', [status(esa)], ['7'])).
% 1.25/1.44  thf('10', plain,
% 1.25/1.44      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('11', plain,
% 1.25/1.44      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.25/1.44       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('split', [status(esa)], ['10'])).
% 1.25/1.44  thf('12', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(t7_xboole_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.25/1.44  thf('13', plain,
% 1.25/1.44      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 1.25/1.44      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.25/1.44  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.25/1.44      inference('sup+', [status(thm)], ['12', '13'])).
% 1.25/1.44  thf(l3_zfmisc_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.25/1.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.25/1.44  thf('15', plain,
% 1.25/1.44      (![X57 : $i, X58 : $i]:
% 1.25/1.44         (((X58) = (k1_tarski @ X57))
% 1.25/1.44          | ((X58) = (k1_xboole_0))
% 1.25/1.44          | ~ (r1_tarski @ X58 @ (k1_tarski @ X57)))),
% 1.25/1.44      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.25/1.44  thf('16', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.25/1.44  thf('17', plain,
% 1.25/1.44      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('18', plain,
% 1.25/1.44      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.25/1.44         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('split', [status(esa)], ['17'])).
% 1.25/1.44  thf('19', plain,
% 1.25/1.44      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 1.25/1.44         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['16', '18'])).
% 1.25/1.44  thf('20', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('simplify', [status(thm)], ['19'])).
% 1.25/1.44  thf('21', plain,
% 1.25/1.44      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.25/1.44      inference('split', [status(esa)], ['7'])).
% 1.25/1.44  thf('22', plain,
% 1.25/1.44      ((((sk_B_1) != (sk_B_1)))
% 1.25/1.44         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.25/1.44             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('sup-', [status(thm)], ['20', '21'])).
% 1.25/1.44  thf('23', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('simplify', [status(thm)], ['22'])).
% 1.25/1.44  thf('24', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sat_resolution*', [status(thm)], ['9', '11', '23'])).
% 1.25/1.44  thf('25', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.25/1.44      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 1.25/1.44  thf('26', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['6', '25'])).
% 1.25/1.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.25/1.44  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.25/1.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.25/1.44  thf('28', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.25/1.44  thf('29', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf(t95_xboole_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( k3_xboole_0 @ A @ B ) =
% 1.25/1.44       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.25/1.44  thf('30', plain,
% 1.25/1.44      (![X22 : $i, X23 : $i]:
% 1.25/1.44         ((k3_xboole_0 @ X22 @ X23)
% 1.25/1.44           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.25/1.44              (k2_xboole_0 @ X22 @ X23)))),
% 1.25/1.44      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.25/1.44  thf(t91_xboole_1, axiom,
% 1.25/1.44    (![A:$i,B:$i,C:$i]:
% 1.25/1.44     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.25/1.44       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.25/1.44  thf('31', plain,
% 1.25/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.25/1.44         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 1.25/1.44           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 1.25/1.44      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.25/1.44  thf('32', plain,
% 1.25/1.44      (![X22 : $i, X23 : $i]:
% 1.25/1.44         ((k3_xboole_0 @ X22 @ X23)
% 1.25/1.44           = (k5_xboole_0 @ X22 @ 
% 1.25/1.44              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 1.25/1.44      inference('demod', [status(thm)], ['30', '31'])).
% 1.25/1.44  thf('33', plain,
% 1.25/1.44      (((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.25/1.44         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('sup+', [status(thm)], ['29', '32'])).
% 1.25/1.44  thf('34', plain,
% 1.25/1.44      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.25/1.44          = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1)))
% 1.25/1.44        | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['28', '33'])).
% 1.25/1.44  thf(commutativity_k5_xboole_0, axiom,
% 1.25/1.44    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.25/1.44  thf('35', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.25/1.44      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.25/1.44  thf(t92_xboole_1, axiom,
% 1.25/1.44    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.25/1.44  thf('36', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.25/1.44  thf('37', plain,
% 1.25/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.25/1.44         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 1.25/1.44           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 1.25/1.44      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.25/1.44  thf('38', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.25/1.44           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['36', '37'])).
% 1.25/1.44  thf(idempotence_k2_xboole_0, axiom,
% 1.25/1.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.25/1.44  thf('39', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 1.25/1.44      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.25/1.44  thf('40', plain,
% 1.25/1.44      (![X22 : $i, X23 : $i]:
% 1.25/1.44         ((k3_xboole_0 @ X22 @ X23)
% 1.25/1.44           = (k5_xboole_0 @ X22 @ 
% 1.25/1.44              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 1.25/1.44      inference('demod', [status(thm)], ['30', '31'])).
% 1.25/1.44  thf('41', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         ((k3_xboole_0 @ X0 @ X0)
% 1.25/1.44           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['39', '40'])).
% 1.25/1.44  thf(idempotence_k3_xboole_0, axiom,
% 1.25/1.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.25/1.44  thf('42', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 1.25/1.44      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.25/1.44  thf('43', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 1.25/1.44      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.25/1.44  thf('44', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.25/1.44      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.25/1.44  thf('45', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.25/1.44      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.25/1.44  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.25/1.44      inference('sup+', [status(thm)], ['44', '45'])).
% 1.25/1.44  thf('47', plain,
% 1.25/1.44      (![X0 : $i, X1 : $i]:
% 1.25/1.44         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['38', '46'])).
% 1.25/1.44  thf('48', plain,
% 1.25/1.44      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 1.25/1.44        | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('demod', [status(thm)], ['34', '35', '47'])).
% 1.25/1.44  thf('49', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.25/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.25/1.44  thf('50', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.25/1.44  thf('51', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['14', '15'])).
% 1.25/1.44  thf(l27_zfmisc_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.25/1.44  thf('52', plain,
% 1.25/1.44      (![X55 : $i, X56 : $i]:
% 1.25/1.44         ((r1_xboole_0 @ (k1_tarski @ X55) @ X56) | (r2_hidden @ X55 @ X56))),
% 1.25/1.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.25/1.44  thf('53', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.25/1.44          | ((sk_B_1) = (k1_xboole_0))
% 1.25/1.44          | (r2_hidden @ sk_A @ X0))),
% 1.25/1.44      inference('sup+', [status(thm)], ['51', '52'])).
% 1.25/1.44  thf(l1_zfmisc_1, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.25/1.44  thf('54', plain,
% 1.25/1.44      (![X52 : $i, X54 : $i]:
% 1.25/1.44         ((r1_tarski @ (k1_tarski @ X52) @ X54) | ~ (r2_hidden @ X52 @ X54))),
% 1.25/1.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.25/1.44  thf('55', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((sk_B_1) = (k1_xboole_0))
% 1.25/1.44          | (r1_xboole_0 @ sk_B_1 @ X0)
% 1.25/1.44          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 1.25/1.44      inference('sup-', [status(thm)], ['53', '54'])).
% 1.25/1.44  thf('56', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         ((r1_tarski @ sk_B_1 @ X0)
% 1.25/1.44          | ((sk_B_1) = (k1_xboole_0))
% 1.25/1.44          | (r1_xboole_0 @ sk_B_1 @ X0)
% 1.25/1.44          | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['50', '55'])).
% 1.25/1.44  thf('57', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.25/1.44          | ((sk_B_1) = (k1_xboole_0))
% 1.25/1.44          | (r1_tarski @ sk_B_1 @ X0))),
% 1.25/1.44      inference('simplify', [status(thm)], ['56'])).
% 1.25/1.44  thf('58', plain,
% 1.25/1.44      (![X14 : $i, X15 : $i]:
% 1.25/1.44         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 1.25/1.44      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.25/1.44  thf('59', plain,
% 1.25/1.44      (![X0 : $i]:
% 1.25/1.44         (((sk_B_1) = (k1_xboole_0))
% 1.25/1.44          | (r1_xboole_0 @ sk_B_1 @ X0)
% 1.25/1.44          | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['57', '58'])).
% 1.25/1.44  thf('60', plain,
% 1.25/1.44      ((((k1_tarski @ sk_A) = (sk_C_1))
% 1.25/1.44        | (r1_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.25/1.44        | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['49', '59'])).
% 1.25/1.44  thf('61', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.25/1.44      inference('simpl_trail', [status(thm)], ['8', '24'])).
% 1.25/1.44  thf('62', plain,
% 1.25/1.44      (((r1_xboole_0 @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 1.25/1.44  thf(d7_xboole_0, axiom,
% 1.25/1.44    (![A:$i,B:$i]:
% 1.25/1.44     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.25/1.44       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.25/1.44  thf('63', plain,
% 1.25/1.44      (![X9 : $i, X10 : $i]:
% 1.25/1.44         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 1.25/1.44          | ~ (r1_xboole_0 @ X9 @ X10))),
% 1.25/1.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.25/1.44  thf('64', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0))
% 1.25/1.44        | ((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['62', '63'])).
% 1.25/1.44  thf('65', plain,
% 1.25/1.44      ((((sk_C_1) = (k1_xboole_0))
% 1.25/1.44        | ((sk_B_1) = (k1_xboole_0))
% 1.25/1.44        | ((sk_B_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sup+', [status(thm)], ['48', '64'])).
% 1.25/1.44  thf('66', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('simplify', [status(thm)], ['65'])).
% 1.25/1.44  thf('67', plain,
% 1.25/1.44      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.25/1.44      inference('split', [status(esa)], ['17'])).
% 1.25/1.44  thf('68', plain,
% 1.25/1.44      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('simplify', [status(thm)], ['19'])).
% 1.25/1.44  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.25/1.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.25/1.44  thf('70', plain,
% 1.25/1.44      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.25/1.44      inference('sup+', [status(thm)], ['68', '69'])).
% 1.25/1.44  thf('71', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['6', '25'])).
% 1.25/1.44  thf('72', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('sup-', [status(thm)], ['70', '71'])).
% 1.25/1.44  thf('73', plain,
% 1.25/1.44      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.25/1.44      inference('split', [status(esa)], ['17'])).
% 1.25/1.44  thf('74', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.25/1.44      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 1.25/1.44  thf('75', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.25/1.44      inference('simpl_trail', [status(thm)], ['67', '74'])).
% 1.25/1.44  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.25/1.44      inference('simplify_reflect-', [status(thm)], ['66', '75'])).
% 1.25/1.44  thf('77', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.25/1.44      inference('demod', [status(thm)], ['27', '76'])).
% 1.25/1.44  thf('78', plain, ($false), inference('demod', [status(thm)], ['26', '77'])).
% 1.25/1.44  
% 1.25/1.44  % SZS output end Refutation
% 1.25/1.44  
% 1.25/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
