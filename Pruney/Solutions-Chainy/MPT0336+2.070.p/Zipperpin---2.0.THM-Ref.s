%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rsWZvb1fbF

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 207 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  819 (1670 expanded)
%              Number of equality atoms :   60 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['33','52','55'])).

thf('57',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73','76','77','82'])).

thf('84',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('91',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rsWZvb1fbF
% 0.16/0.37  % Computer   : n004.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:11:39 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.96/2.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.96/2.13  % Solved by: fo/fo7.sh
% 1.96/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.13  % done 5037 iterations in 1.639s
% 1.96/2.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.96/2.13  % SZS output start Refutation
% 1.96/2.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.96/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.96/2.13  thf(sk_B_type, type, sk_B: $i).
% 1.96/2.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.96/2.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.96/2.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.96/2.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.96/2.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.96/2.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.96/2.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.96/2.13  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.96/2.13  thf(sk_D_type, type, sk_D: $i).
% 1.96/2.13  thf(t149_zfmisc_1, conjecture,
% 1.96/2.13    (![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.13     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.96/2.13         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.96/2.13       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.96/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.13    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.13        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.96/2.13            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.96/2.13          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.96/2.13    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.96/2.13  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf(d7_xboole_0, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.96/2.13       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.96/2.13  thf('2', plain,
% 1.96/2.13      (![X2 : $i, X3 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.96/2.13  thf(commutativity_k3_xboole_0, axiom,
% 1.96/2.13    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.96/2.13  thf('4', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.96/2.13      inference('demod', [status(thm)], ['3', '4'])).
% 1.96/2.13  thf('6', plain,
% 1.96/2.13      (![X2 : $i, X4 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('7', plain,
% 1.96/2.13      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 1.96/2.13      inference('sup-', [status(thm)], ['5', '6'])).
% 1.96/2.13  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.96/2.13      inference('simplify', [status(thm)], ['7'])).
% 1.96/2.13  thf(t65_zfmisc_1, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.96/2.13       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.96/2.13  thf('9', plain,
% 1.96/2.13      (![X39 : $i, X40 : $i]:
% 1.96/2.13         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 1.96/2.13          | (r2_hidden @ X40 @ X39))),
% 1.96/2.13      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.96/2.13  thf(t79_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.96/2.13  thf('10', plain,
% 1.96/2.13      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 1.96/2.13      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.96/2.13  thf(symmetry_r1_xboole_0, axiom,
% 1.96/2.13    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.96/2.13  thf('11', plain,
% 1.96/2.13      (![X5 : $i, X6 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.96/2.13      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.96/2.13  thf('12', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['10', '11'])).
% 1.96/2.13  thf('13', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 1.96/2.13      inference('sup+', [status(thm)], ['9', '12'])).
% 1.96/2.13  thf(t70_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i,C:$i]:
% 1.96/2.13     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.96/2.13            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.96/2.13       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.96/2.13            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.96/2.13  thf('14', plain,
% 1.96/2.13      (![X18 : $i, X19 : $i, X21 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X18 @ X19)
% 1.96/2.13          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.96/2.13  thf('15', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.96/2.13          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.96/2.13      inference('sup-', [status(thm)], ['13', '14'])).
% 1.96/2.13  thf('16', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf('17', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf('18', plain,
% 1.96/2.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.96/2.13          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.96/2.13          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.96/2.13      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.96/2.13  thf('19', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 1.96/2.13          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.96/2.13      inference('sup-', [status(thm)], ['17', '18'])).
% 1.96/2.13  thf('20', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.96/2.13      inference('sup-', [status(thm)], ['16', '19'])).
% 1.96/2.13  thf('21', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf(t3_xboole_0, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.96/2.13            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.96/2.13       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.96/2.13            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.96/2.13  thf('22', plain,
% 1.96/2.13      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.96/2.13         (~ (r2_hidden @ X9 @ X7)
% 1.96/2.13          | ~ (r2_hidden @ X9 @ X10)
% 1.96/2.13          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.96/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.96/2.13  thf('23', plain,
% 1.96/2.13      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['21', '22'])).
% 1.96/2.13  thf('24', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.96/2.13      inference('sup-', [status(thm)], ['20', '23'])).
% 1.96/2.13  thf('25', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.96/2.13      inference('sup-', [status(thm)], ['15', '24'])).
% 1.96/2.13  thf('26', plain,
% 1.96/2.13      (![X2 : $i, X3 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('27', plain,
% 1.96/2.13      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['25', '26'])).
% 1.96/2.13  thf('28', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('29', plain,
% 1.96/2.13      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 1.96/2.13      inference('demod', [status(thm)], ['27', '28'])).
% 1.96/2.13  thf('30', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf(t16_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i,C:$i]:
% 1.96/2.13     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.96/2.13       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.96/2.13  thf('31', plain,
% 1.96/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.96/2.13           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.96/2.13  thf('32', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.96/2.13           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['30', '31'])).
% 1.96/2.13  thf('33', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.96/2.13           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['29', '32'])).
% 1.96/2.13  thf(t48_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.96/2.13  thf('34', plain,
% 1.96/2.13      (![X16 : $i, X17 : $i]:
% 1.96/2.13         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.96/2.13           = (k3_xboole_0 @ X16 @ X17))),
% 1.96/2.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.96/2.13  thf('35', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['10', '11'])).
% 1.96/2.13  thf(t83_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.96/2.13  thf('36', plain,
% 1.96/2.13      (![X27 : $i, X28 : $i]:
% 1.96/2.13         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 1.96/2.13      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.96/2.13  thf('37', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['35', '36'])).
% 1.96/2.13  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.96/2.13      inference('sup+', [status(thm)], ['34', '37'])).
% 1.96/2.13  thf('39', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('40', plain,
% 1.96/2.13      (![X2 : $i, X4 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('41', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('sup-', [status(thm)], ['39', '40'])).
% 1.96/2.13  thf('42', plain,
% 1.96/2.13      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['38', '41'])).
% 1.96/2.13  thf('43', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.96/2.13      inference('simplify', [status(thm)], ['42'])).
% 1.96/2.13  thf('44', plain,
% 1.96/2.13      (![X7 : $i, X8 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.96/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.96/2.13  thf('45', plain,
% 1.96/2.13      (![X7 : $i, X8 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.96/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.96/2.13  thf('46', plain,
% 1.96/2.13      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.96/2.13         (~ (r2_hidden @ X9 @ X7)
% 1.96/2.13          | ~ (r2_hidden @ X9 @ X10)
% 1.96/2.13          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.96/2.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.96/2.13  thf('47', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X0 @ X1)
% 1.96/2.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.96/2.13          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.96/2.13      inference('sup-', [status(thm)], ['45', '46'])).
% 1.96/2.13  thf('48', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X0 @ X1)
% 1.96/2.13          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.96/2.13          | (r1_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('sup-', [status(thm)], ['44', '47'])).
% 1.96/2.13  thf('49', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('simplify', [status(thm)], ['48'])).
% 1.96/2.13  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.96/2.13      inference('sup-', [status(thm)], ['43', '49'])).
% 1.96/2.13  thf('51', plain,
% 1.96/2.13      (![X2 : $i, X3 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('52', plain,
% 1.96/2.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['50', '51'])).
% 1.96/2.13  thf('53', plain,
% 1.96/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.96/2.13           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.96/2.13  thf('54', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('55', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.96/2.13           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['53', '54'])).
% 1.96/2.13  thf('56', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         ((k1_xboole_0)
% 1.96/2.13           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D))))),
% 1.96/2.13      inference('demod', [status(thm)], ['33', '52', '55'])).
% 1.96/2.13  thf('57', plain,
% 1.96/2.13      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.96/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.13  thf('58', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('59', plain,
% 1.96/2.13      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.96/2.13      inference('demod', [status(thm)], ['57', '58'])).
% 1.96/2.13  thf(t28_xboole_1, axiom,
% 1.96/2.13    (![A:$i,B:$i]:
% 1.96/2.13     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.96/2.13  thf('60', plain,
% 1.96/2.13      (![X14 : $i, X15 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.96/2.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.96/2.13  thf('61', plain,
% 1.96/2.13      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.96/2.13         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.96/2.13      inference('sup-', [status(thm)], ['59', '60'])).
% 1.96/2.13  thf('62', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('63', plain,
% 1.96/2.13      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.96/2.13         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.96/2.13      inference('demod', [status(thm)], ['61', '62'])).
% 1.96/2.13  thf('64', plain,
% 1.96/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.96/2.13           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.96/2.13  thf('65', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 1.96/2.13           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 1.96/2.13              (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['63', '64'])).
% 1.96/2.13  thf('66', plain,
% 1.96/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.96/2.13           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.96/2.13  thf('67', plain,
% 1.96/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.96/2.13           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.96/2.13      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.96/2.13  thf('68', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 1.96/2.13           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ 
% 1.96/2.13              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 1.96/2.13      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.96/2.13  thf('69', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.96/2.13           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['53', '54'])).
% 1.96/2.13  thf('70', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.96/2.13           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['30', '31'])).
% 1.96/2.13  thf('71', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 1.96/2.13           = (k3_xboole_0 @ sk_B @ 
% 1.96/2.13              (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))))),
% 1.96/2.13      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.96/2.13  thf('72', plain,
% 1.96/2.13      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.96/2.13         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.96/2.13      inference('sup+', [status(thm)], ['56', '71'])).
% 1.96/2.13  thf('73', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('74', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.96/2.13      inference('sup+', [status(thm)], ['34', '37'])).
% 1.96/2.13  thf('75', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.96/2.13           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['53', '54'])).
% 1.96/2.13  thf('76', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]:
% 1.96/2.13         ((k3_xboole_0 @ X1 @ X0)
% 1.96/2.13           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.96/2.13      inference('sup+', [status(thm)], ['74', '75'])).
% 1.96/2.13  thf('77', plain,
% 1.96/2.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.96/2.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.96/2.13  thf('78', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.96/2.13      inference('sup-', [status(thm)], ['43', '49'])).
% 1.96/2.13  thf('79', plain,
% 1.96/2.13      (![X5 : $i, X6 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.96/2.13      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.96/2.13  thf('80', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.96/2.13      inference('sup-', [status(thm)], ['78', '79'])).
% 1.96/2.13  thf('81', plain,
% 1.96/2.13      (![X2 : $i, X3 : $i]:
% 1.96/2.13         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('82', plain,
% 1.96/2.13      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.96/2.13      inference('sup-', [status(thm)], ['80', '81'])).
% 1.96/2.13  thf('83', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.96/2.13      inference('demod', [status(thm)], ['72', '73', '76', '77', '82'])).
% 1.96/2.13  thf('84', plain,
% 1.96/2.13      (![X2 : $i, X4 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.96/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.96/2.13  thf('85', plain,
% 1.96/2.13      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.96/2.13      inference('sup-', [status(thm)], ['83', '84'])).
% 1.96/2.13  thf('86', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.96/2.13      inference('simplify', [status(thm)], ['85'])).
% 1.96/2.13  thf('87', plain,
% 1.96/2.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.96/2.13          | ~ (r1_xboole_0 @ X18 @ X19)
% 1.96/2.13          | ~ (r1_xboole_0 @ X18 @ X20))),
% 1.96/2.13      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.96/2.13  thf('88', plain,
% 1.96/2.13      (![X0 : $i]:
% 1.96/2.13         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.96/2.13          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.96/2.13      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.13  thf('89', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.96/2.13      inference('sup-', [status(thm)], ['8', '88'])).
% 1.96/2.13  thf('90', plain,
% 1.96/2.13      (![X5 : $i, X6 : $i]:
% 1.96/2.13         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.96/2.13      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.96/2.13  thf('91', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.96/2.13      inference('sup-', [status(thm)], ['89', '90'])).
% 1.96/2.13  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 1.96/2.13  
% 1.96/2.13  % SZS output end Refutation
% 1.96/2.13  
% 1.96/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
