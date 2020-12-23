%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oRz7W08j9y

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:05 EST 2020

% Result     : Theorem 54.59s
% Output     : Refutation 54.59s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 279 expanded)
%              Number of leaves         :   23 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  998 (2179 expanded)
%              Number of equality atoms :   99 ( 245 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X39 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('56',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','64'])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['82','94'])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('103',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    sk_B_1 = sk_A ),
    inference(demod,[status(thm)],['17','26','27','103'])).

thf('105',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oRz7W08j9y
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 54.59/54.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.59/54.80  % Solved by: fo/fo7.sh
% 54.59/54.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.59/54.80  % done 29250 iterations in 54.336s
% 54.59/54.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.59/54.80  % SZS output start Refutation
% 54.59/54.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.59/54.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.59/54.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 54.59/54.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 54.59/54.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.59/54.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 54.59/54.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 54.59/54.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 54.59/54.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 54.59/54.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 54.59/54.80  thf(sk_A_type, type, sk_A: $i).
% 54.59/54.80  thf(sk_B_type, type, sk_B: $i > $i).
% 54.59/54.80  thf(t7_xboole_0, axiom,
% 54.59/54.80    (![A:$i]:
% 54.59/54.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 54.59/54.80          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 54.59/54.80  thf('0', plain,
% 54.59/54.80      (![X18 : $i]:
% 54.59/54.80         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 54.59/54.80      inference('cnf', [status(esa)], [t7_xboole_0])).
% 54.59/54.80  thf(d3_tarski, axiom,
% 54.59/54.80    (![A:$i,B:$i]:
% 54.59/54.80     ( ( r1_tarski @ A @ B ) <=>
% 54.59/54.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 54.59/54.80  thf('1', plain,
% 54.59/54.80      (![X3 : $i, X5 : $i]:
% 54.59/54.80         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 54.59/54.80      inference('cnf', [status(esa)], [d3_tarski])).
% 54.59/54.80  thf(l54_zfmisc_1, axiom,
% 54.59/54.80    (![A:$i,B:$i,C:$i,D:$i]:
% 54.59/54.80     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 54.59/54.80       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 54.59/54.80  thf('2', plain,
% 54.59/54.80      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 54.59/54.80         ((r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X39))
% 54.59/54.80          | ~ (r2_hidden @ X37 @ X39)
% 54.59/54.80          | ~ (r2_hidden @ X35 @ X36))),
% 54.59/54.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.59/54.80  thf('3', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.59/54.80         ((r1_tarski @ X0 @ X1)
% 54.59/54.80          | ~ (r2_hidden @ X3 @ X2)
% 54.59/54.80          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 54.59/54.80             (k2_zfmisc_1 @ X2 @ X0)))),
% 54.59/54.80      inference('sup-', [status(thm)], ['1', '2'])).
% 54.59/54.80  thf('4', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.59/54.80         (((X0) = (k1_xboole_0))
% 54.59/54.80          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 54.59/54.80             (k2_zfmisc_1 @ X0 @ X1))
% 54.59/54.80          | (r1_tarski @ X1 @ X2))),
% 54.59/54.80      inference('sup-', [status(thm)], ['0', '3'])).
% 54.59/54.80  thf(t114_zfmisc_1, conjecture,
% 54.59/54.80    (![A:$i,B:$i]:
% 54.59/54.80     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 54.59/54.80       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 54.59/54.80         ( ( A ) = ( B ) ) ) ))).
% 54.59/54.80  thf(zf_stmt_0, negated_conjecture,
% 54.59/54.80    (~( ![A:$i,B:$i]:
% 54.59/54.80        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 54.59/54.80          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 54.59/54.80            ( ( A ) = ( B ) ) ) ) )),
% 54.59/54.80    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 54.59/54.80  thf('5', plain,
% 54.59/54.80      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 54.59/54.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.59/54.80  thf('6', plain,
% 54.59/54.80      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 54.59/54.80         ((r2_hidden @ X37 @ X38)
% 54.59/54.80          | ~ (r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X38)))),
% 54.59/54.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.59/54.80  thf('7', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 54.59/54.80          | (r2_hidden @ X0 @ sk_A))),
% 54.59/54.80      inference('sup-', [status(thm)], ['5', '6'])).
% 54.59/54.80  thf('8', plain,
% 54.59/54.80      (![X0 : $i]:
% 54.59/54.80         ((r1_tarski @ sk_B_1 @ X0)
% 54.59/54.80          | ((sk_A) = (k1_xboole_0))
% 54.59/54.80          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 54.59/54.80      inference('sup-', [status(thm)], ['4', '7'])).
% 54.59/54.80  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 54.59/54.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.59/54.80  thf('10', plain,
% 54.59/54.80      (![X0 : $i]:
% 54.59/54.80         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 54.59/54.80      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 54.59/54.80  thf('11', plain,
% 54.59/54.80      (![X3 : $i, X5 : $i]:
% 54.59/54.80         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 54.59/54.80      inference('cnf', [status(esa)], [d3_tarski])).
% 54.59/54.80  thf('12', plain,
% 54.59/54.80      (((r1_tarski @ sk_B_1 @ sk_A) | (r1_tarski @ sk_B_1 @ sk_A))),
% 54.59/54.80      inference('sup-', [status(thm)], ['10', '11'])).
% 54.59/54.80  thf('13', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 54.59/54.80      inference('simplify', [status(thm)], ['12'])).
% 54.59/54.80  thf(l32_xboole_1, axiom,
% 54.59/54.80    (![A:$i,B:$i]:
% 54.59/54.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 54.59/54.80  thf('14', plain,
% 54.59/54.80      (![X19 : $i, X21 : $i]:
% 54.59/54.80         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 54.59/54.80          | ~ (r1_tarski @ X19 @ X21))),
% 54.59/54.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 54.59/54.80  thf('15', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 54.59/54.80      inference('sup-', [status(thm)], ['13', '14'])).
% 54.59/54.80  thf(t48_xboole_1, axiom,
% 54.59/54.80    (![A:$i,B:$i]:
% 54.59/54.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 54.59/54.80  thf('16', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('17', plain,
% 54.59/54.80      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 54.59/54.80      inference('sup+', [status(thm)], ['15', '16'])).
% 54.59/54.80  thf(idempotence_k3_xboole_0, axiom,
% 54.59/54.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 54.59/54.80  thf('18', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 54.59/54.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 54.59/54.80  thf(t17_xboole_1, axiom,
% 54.59/54.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 54.59/54.80  thf('19', plain,
% 54.59/54.80      (![X27 : $i, X28 : $i]: (r1_tarski @ (k3_xboole_0 @ X27 @ X28) @ X27)),
% 54.59/54.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.59/54.80  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 54.59/54.80      inference('sup+', [status(thm)], ['18', '19'])).
% 54.59/54.80  thf('21', plain,
% 54.59/54.80      (![X19 : $i, X21 : $i]:
% 54.59/54.80         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 54.59/54.80          | ~ (r1_tarski @ X19 @ X21))),
% 54.59/54.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 54.59/54.80  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 54.59/54.80      inference('sup-', [status(thm)], ['20', '21'])).
% 54.59/54.80  thf('23', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('24', plain,
% 54.59/54.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['22', '23'])).
% 54.59/54.80  thf('25', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 54.59/54.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 54.59/54.80  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['24', '25'])).
% 54.59/54.80  thf(commutativity_k3_xboole_0, axiom,
% 54.59/54.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 54.59/54.80  thf('27', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf(t112_xboole_1, axiom,
% 54.59/54.80    (![A:$i,B:$i,C:$i]:
% 54.59/54.80     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 54.59/54.80       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 54.59/54.80  thf('28', plain,
% 54.59/54.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 54.59/54.80      inference('cnf', [status(esa)], [t112_xboole_1])).
% 54.59/54.80  thf('29', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('30', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 54.59/54.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 54.59/54.80  thf('31', plain,
% 54.59/54.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 54.59/54.80      inference('cnf', [status(esa)], [t112_xboole_1])).
% 54.59/54.80  thf('32', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['30', '31'])).
% 54.59/54.80  thf('33', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('34', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 54.59/54.80           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('demod', [status(thm)], ['32', '33'])).
% 54.59/54.80  thf('35', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 54.59/54.80           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['29', '34'])).
% 54.59/54.80  thf('36', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k3_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 54.59/54.80           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 54.59/54.80              (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 54.59/54.80      inference('sup+', [status(thm)], ['28', '35'])).
% 54.59/54.80  thf('37', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 54.59/54.80           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['29', '34'])).
% 54.59/54.80  thf('38', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('39', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf(t100_xboole_1, axiom,
% 54.59/54.80    (![A:$i,B:$i]:
% 54.59/54.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 54.59/54.80  thf('40', plain,
% 54.59/54.80      (![X22 : $i, X23 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X22 @ X23)
% 54.59/54.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 54.59/54.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 54.59/54.80  thf('41', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X0 @ X1)
% 54.59/54.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['39', '40'])).
% 54.59/54.80  thf('42', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('43', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 54.59/54.80           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('demod', [status(thm)], ['36', '37', '38', '41', '42'])).
% 54.59/54.80  thf('44', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('45', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('46', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('47', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['45', '46'])).
% 54.59/54.80  thf('48', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 54.59/54.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 54.59/54.80  thf('49', plain,
% 54.59/54.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 54.59/54.80      inference('cnf', [status(esa)], [t112_xboole_1])).
% 54.59/54.80  thf('50', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['48', '49'])).
% 54.59/54.80  thf('51', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('52', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 54.59/54.80      inference('demod', [status(thm)], ['50', '51'])).
% 54.59/54.80  thf('53', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X0 @ X1)
% 54.59/54.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['39', '40'])).
% 54.59/54.80  thf('54', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X1 @ X0)
% 54.59/54.80           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['52', '53'])).
% 54.59/54.80  thf('55', plain,
% 54.59/54.80      (![X27 : $i, X28 : $i]: (r1_tarski @ (k3_xboole_0 @ X27 @ X28) @ X27)),
% 54.59/54.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 54.59/54.80  thf('56', plain,
% 54.59/54.80      (![X19 : $i, X21 : $i]:
% 54.59/54.80         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 54.59/54.80          | ~ (r1_tarski @ X19 @ X21))),
% 54.59/54.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 54.59/54.80  thf('57', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 54.59/54.80      inference('sup-', [status(thm)], ['55', '56'])).
% 54.59/54.80  thf('58', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['54', '57'])).
% 54.59/54.80  thf('59', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('60', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 54.59/54.80           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['58', '59'])).
% 54.59/54.80  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['24', '25'])).
% 54.59/54.80  thf('62', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('63', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X0 @ X1)
% 54.59/54.80           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 54.59/54.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 54.59/54.80  thf('64', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k4_xboole_0 @ X1 @ X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['47', '63'])).
% 54.59/54.80  thf('65', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k4_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('sup+', [status(thm)], ['44', '64'])).
% 54.59/54.80  thf('66', plain,
% 54.59/54.80      (![X22 : $i, X23 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X22 @ X23)
% 54.59/54.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 54.59/54.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 54.59/54.80  thf('67', plain,
% 54.59/54.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 54.59/54.80         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 54.59/54.80      inference('cnf', [status(esa)], [t112_xboole_1])).
% 54.59/54.80  thf('68', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 54.59/54.80           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['66', '67'])).
% 54.59/54.80  thf('69', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('70', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 54.59/54.80      inference('sup-', [status(thm)], ['55', '56'])).
% 54.59/54.80  thf('71', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 54.59/54.80      inference('sup+', [status(thm)], ['69', '70'])).
% 54.59/54.80  thf('72', plain,
% 54.59/54.80      (![X22 : $i, X23 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X22 @ X23)
% 54.59/54.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 54.59/54.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 54.59/54.80  thf('73', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('74', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('demod', [status(thm)], ['68', '71', '72', '73'])).
% 54.59/54.80  thf('75', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k1_xboole_0)
% 54.59/54.80           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 54.59/54.80      inference('sup+', [status(thm)], ['65', '74'])).
% 54.59/54.80  thf('76', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 54.59/54.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 54.59/54.80  thf('77', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k1_xboole_0)
% 54.59/54.80           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 54.59/54.80      inference('demod', [status(thm)], ['75', '76'])).
% 54.59/54.80  thf('78', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 54.59/54.80           = (k1_xboole_0))),
% 54.59/54.80      inference('demod', [status(thm)], ['43', '77'])).
% 54.59/54.80  thf('79', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 54.59/54.80           = (k4_xboole_0 @ X1 @ X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['47', '63'])).
% 54.59/54.80  thf('80', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 54.59/54.80           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 54.59/54.80      inference('sup+', [status(thm)], ['78', '79'])).
% 54.59/54.80  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['24', '25'])).
% 54.59/54.80  thf('82', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((X1)
% 54.59/54.80           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 54.59/54.80      inference('demod', [status(thm)], ['80', '81'])).
% 54.59/54.80  thf('83', plain,
% 54.59/54.80      (![X3 : $i, X5 : $i]:
% 54.59/54.80         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 54.59/54.80      inference('cnf', [status(esa)], [d3_tarski])).
% 54.59/54.80  thf('84', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.59/54.80         ((r1_tarski @ X0 @ X1)
% 54.59/54.80          | ~ (r2_hidden @ X3 @ X2)
% 54.59/54.80          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 54.59/54.80             (k2_zfmisc_1 @ X2 @ X0)))),
% 54.59/54.80      inference('sup-', [status(thm)], ['1', '2'])).
% 54.59/54.80  thf('85', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 54.59/54.80         ((r1_tarski @ X0 @ X1)
% 54.59/54.80          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 54.59/54.80             (k2_zfmisc_1 @ X0 @ X2))
% 54.59/54.80          | (r1_tarski @ X2 @ X3))),
% 54.59/54.80      inference('sup-', [status(thm)], ['83', '84'])).
% 54.59/54.80  thf('86', plain,
% 54.59/54.80      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 54.59/54.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.59/54.80  thf('87', plain,
% 54.59/54.80      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 54.59/54.80         ((r2_hidden @ X35 @ X36)
% 54.59/54.80          | ~ (r2_hidden @ (k4_tarski @ X35 @ X37) @ (k2_zfmisc_1 @ X36 @ X38)))),
% 54.59/54.80      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 54.59/54.80  thf('88', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 54.59/54.80          | (r2_hidden @ X1 @ sk_B_1))),
% 54.59/54.80      inference('sup-', [status(thm)], ['86', '87'])).
% 54.59/54.80  thf('89', plain,
% 54.59/54.80      (![X0 : $i, X1 : $i]:
% 54.59/54.80         ((r1_tarski @ sk_B_1 @ X0)
% 54.59/54.80          | (r1_tarski @ sk_A @ X1)
% 54.59/54.80          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B_1))),
% 54.59/54.80      inference('sup-', [status(thm)], ['85', '88'])).
% 54.59/54.80  thf('90', plain,
% 54.59/54.80      (![X3 : $i, X5 : $i]:
% 54.59/54.80         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 54.59/54.80      inference('cnf', [status(esa)], [d3_tarski])).
% 54.59/54.80  thf('91', plain,
% 54.59/54.80      (![X0 : $i]:
% 54.59/54.80         ((r1_tarski @ sk_A @ sk_B_1)
% 54.59/54.80          | (r1_tarski @ sk_B_1 @ X0)
% 54.59/54.80          | (r1_tarski @ sk_A @ sk_B_1))),
% 54.59/54.80      inference('sup-', [status(thm)], ['89', '90'])).
% 54.59/54.80  thf('92', plain,
% 54.59/54.80      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | (r1_tarski @ sk_A @ sk_B_1))),
% 54.59/54.80      inference('simplify', [status(thm)], ['91'])).
% 54.59/54.80  thf('93', plain,
% 54.59/54.80      (![X19 : $i, X21 : $i]:
% 54.59/54.80         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 54.59/54.80          | ~ (r1_tarski @ X19 @ X21))),
% 54.59/54.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 54.59/54.80  thf('94', plain,
% 54.59/54.80      (![X0 : $i]:
% 54.59/54.80         ((r1_tarski @ sk_A @ sk_B_1)
% 54.59/54.80          | ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 54.59/54.80      inference('sup-', [status(thm)], ['92', '93'])).
% 54.59/54.80  thf('95', plain,
% 54.59/54.80      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_1))),
% 54.59/54.80      inference('sup+', [status(thm)], ['82', '94'])).
% 54.59/54.80  thf('96', plain, (((sk_B_1) != (k1_xboole_0))),
% 54.59/54.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.59/54.80  thf('97', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 54.59/54.80      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 54.59/54.80  thf('98', plain,
% 54.59/54.80      (![X19 : $i, X21 : $i]:
% 54.59/54.80         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 54.59/54.80          | ~ (r1_tarski @ X19 @ X21))),
% 54.59/54.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 54.59/54.80  thf('99', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 54.59/54.80      inference('sup-', [status(thm)], ['97', '98'])).
% 54.59/54.80  thf('100', plain,
% 54.59/54.80      (![X29 : $i, X30 : $i]:
% 54.59/54.80         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X29 @ X30))
% 54.59/54.80           = (k3_xboole_0 @ X29 @ X30))),
% 54.59/54.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 54.59/54.80  thf('101', plain,
% 54.59/54.80      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 54.59/54.80      inference('sup+', [status(thm)], ['99', '100'])).
% 54.59/54.80  thf('102', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 54.59/54.80      inference('demod', [status(thm)], ['24', '25'])).
% 54.59/54.80  thf('103', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 54.59/54.80      inference('demod', [status(thm)], ['101', '102'])).
% 54.59/54.80  thf('104', plain, (((sk_B_1) = (sk_A))),
% 54.59/54.80      inference('demod', [status(thm)], ['17', '26', '27', '103'])).
% 54.59/54.80  thf('105', plain, (((sk_A) != (sk_B_1))),
% 54.59/54.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.59/54.80  thf('106', plain, ($false),
% 54.59/54.80      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 54.59/54.80  
% 54.59/54.80  % SZS output end Refutation
% 54.59/54.80  
% 54.59/54.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
