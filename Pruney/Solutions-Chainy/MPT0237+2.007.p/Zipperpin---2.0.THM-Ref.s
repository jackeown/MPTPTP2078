%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AHnlHsYXZl

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:59 EST 2020

% Result     : Theorem 37.56s
% Output     : Refutation 37.56s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 616 expanded)
%              Number of leaves         :   34 ( 212 expanded)
%              Depth                    :   22
%              Number of atoms          :  912 (4675 expanded)
%              Number of equality atoms :  101 ( 494 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X60 ) @ ( k1_tarski @ X61 ) )
        = ( k2_tarski @ X60 @ X61 ) )
      | ( X60 = X61 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['10','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','66','67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ k1_xboole_0 )
        = ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['38','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','65'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X1 )
        = ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_enumset1 @ X1 @ X0 @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_enumset1 @ X1 @ X0 @ X0 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['9','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_enumset1 @ X1 @ X0 @ X0 )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('83',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['83'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('86',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('87',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['83'])).

thf('90',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('91',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','84','85','88','89','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AHnlHsYXZl
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 37.56/37.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 37.56/37.80  % Solved by: fo/fo7.sh
% 37.56/37.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.56/37.80  % done 43769 iterations in 37.296s
% 37.56/37.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 37.56/37.80  % SZS output start Refutation
% 37.56/37.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 37.56/37.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 37.56/37.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 37.56/37.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 37.56/37.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 37.56/37.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 37.56/37.80  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 37.56/37.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 37.56/37.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.56/37.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 37.56/37.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 37.56/37.80  thf(sk_A_type, type, sk_A: $i).
% 37.56/37.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 37.56/37.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 37.56/37.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 37.56/37.80  thf(sk_B_type, type, sk_B: $i).
% 37.56/37.80  thf(t32_zfmisc_1, conjecture,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 37.56/37.80       ( k2_tarski @ A @ B ) ))).
% 37.56/37.80  thf(zf_stmt_0, negated_conjecture,
% 37.56/37.80    (~( ![A:$i,B:$i]:
% 37.56/37.80        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 37.56/37.80          ( k2_tarski @ A @ B ) ) )),
% 37.56/37.80    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 37.56/37.80  thf('0', plain,
% 37.56/37.80      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 37.56/37.80         != (k2_tarski @ sk_A @ sk_B))),
% 37.56/37.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.56/37.80  thf(l51_zfmisc_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 37.56/37.80  thf('1', plain,
% 37.56/37.80      (![X58 : $i, X59 : $i]:
% 37.56/37.80         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 37.56/37.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 37.56/37.80  thf('2', plain,
% 37.56/37.80      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 37.56/37.80         != (k2_tarski @ sk_A @ sk_B))),
% 37.56/37.80      inference('demod', [status(thm)], ['0', '1'])).
% 37.56/37.80  thf(t69_enumset1, axiom,
% 37.56/37.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 37.56/37.80  thf('3', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 37.56/37.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.56/37.80  thf(t42_enumset1, axiom,
% 37.56/37.80    (![A:$i,B:$i,C:$i]:
% 37.56/37.80     ( ( k1_enumset1 @ A @ B @ C ) =
% 37.56/37.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 37.56/37.80  thf('4', plain,
% 37.56/37.80      (![X32 : $i, X33 : $i, X34 : $i]:
% 37.56/37.80         ((k1_enumset1 @ X32 @ X33 @ X34)
% 37.56/37.80           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t42_enumset1])).
% 37.56/37.80  thf('5', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k1_enumset1 @ X1 @ X0 @ X0)
% 37.56/37.80           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['3', '4'])).
% 37.56/37.80  thf('6', plain,
% 37.56/37.80      (((k1_enumset1 @ sk_A @ sk_B @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 37.56/37.80      inference('demod', [status(thm)], ['2', '5'])).
% 37.56/37.80  thf('7', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 37.56/37.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.56/37.80  thf(t29_zfmisc_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( ( A ) != ( B ) ) =>
% 37.56/37.80       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 37.56/37.80         ( k2_tarski @ A @ B ) ) ))).
% 37.56/37.80  thf('8', plain,
% 37.56/37.80      (![X60 : $i, X61 : $i]:
% 37.56/37.80         (((k5_xboole_0 @ (k1_tarski @ X60) @ (k1_tarski @ X61))
% 37.56/37.80            = (k2_tarski @ X60 @ X61))
% 37.56/37.80          | ((X60) = (X61)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 37.56/37.80  thf('9', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 37.56/37.80            = (k2_tarski @ X1 @ X0))
% 37.56/37.80          | ((X1) = (X0)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['7', '8'])).
% 37.56/37.80  thf('10', plain,
% 37.56/37.80      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 37.56/37.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.56/37.80  thf(t4_xboole_0, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 37.56/37.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 37.56/37.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 37.56/37.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 37.56/37.80  thf('11', plain,
% 37.56/37.80      (![X6 : $i, X7 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ X6 @ X7)
% 37.56/37.80          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 37.56/37.80  thf(t48_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 37.56/37.80  thf('12', plain,
% 37.56/37.80      (![X21 : $i, X22 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 37.56/37.80           = (k3_xboole_0 @ X21 @ X22))),
% 37.56/37.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 37.56/37.80  thf(t36_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 37.56/37.80  thf('13', plain,
% 37.56/37.80      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 37.56/37.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 37.56/37.80  thf(d3_tarski, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( r1_tarski @ A @ B ) <=>
% 37.56/37.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 37.56/37.80  thf('14', plain,
% 37.56/37.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X2 @ X3)
% 37.56/37.80          | (r2_hidden @ X2 @ X4)
% 37.56/37.80          | ~ (r1_tarski @ X3 @ X4))),
% 37.56/37.80      inference('cnf', [status(esa)], [d3_tarski])).
% 37.56/37.80  thf('15', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['13', '14'])).
% 37.56/37.80  thf('16', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 37.56/37.80      inference('sup-', [status(thm)], ['12', '15'])).
% 37.56/37.80  thf('17', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 37.56/37.80      inference('sup-', [status(thm)], ['11', '16'])).
% 37.56/37.80  thf(d1_tarski, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 37.56/37.80       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 37.56/37.80  thf('18', plain,
% 37.56/37.80      (![X27 : $i, X29 : $i, X30 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X30 @ X29)
% 37.56/37.80          | ((X30) = (X27))
% 37.56/37.80          | ((X29) != (k1_tarski @ X27)))),
% 37.56/37.80      inference('cnf', [status(esa)], [d1_tarski])).
% 37.56/37.80  thf('19', plain,
% 37.56/37.80      (![X27 : $i, X30 : $i]:
% 37.56/37.80         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 37.56/37.80      inference('simplify', [status(thm)], ['18'])).
% 37.56/37.80  thf('20', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 37.56/37.80          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['17', '19'])).
% 37.56/37.80  thf('21', plain,
% 37.56/37.80      (![X6 : $i, X7 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ X6 @ X7)
% 37.56/37.80          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 37.56/37.80  thf(commutativity_k3_xboole_0, axiom,
% 37.56/37.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 37.56/37.80  thf('22', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 37.56/37.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 37.56/37.80  thf('23', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 37.56/37.80      inference('sup-', [status(thm)], ['12', '15'])).
% 37.56/37.80  thf('24', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['22', '23'])).
% 37.56/37.80  thf('25', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['21', '24'])).
% 37.56/37.80  thf('26', plain,
% 37.56/37.80      (![X27 : $i, X30 : $i]:
% 37.56/37.80         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 37.56/37.80      inference('simplify', [status(thm)], ['18'])).
% 37.56/37.80  thf('27', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 37.56/37.80          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['25', '26'])).
% 37.56/37.80  thf('28', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((X0) = (X1))
% 37.56/37.80          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 37.56/37.80          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['20', '27'])).
% 37.56/37.80  thf('29', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 37.56/37.80      inference('simplify', [status(thm)], ['28'])).
% 37.56/37.80  thf('30', plain,
% 37.56/37.80      (![X3 : $i, X5 : $i]:
% 37.56/37.80         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 37.56/37.80      inference('cnf', [status(esa)], [d3_tarski])).
% 37.56/37.80  thf('31', plain,
% 37.56/37.80      (![X6 : $i, X8 : $i, X9 : $i]:
% 37.56/37.80         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 37.56/37.80          | ~ (r1_xboole_0 @ X6 @ X9))),
% 37.56/37.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 37.56/37.80  thf('32', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 37.56/37.80          | ~ (r1_xboole_0 @ X1 @ X0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['30', '31'])).
% 37.56/37.80  thf('33', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.56/37.80         (((X1) = (X0))
% 37.56/37.80          | (r1_tarski @ (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 37.56/37.80             X2))),
% 37.56/37.80      inference('sup-', [status(thm)], ['29', '32'])).
% 37.56/37.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 37.56/37.80  thf('34', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 37.56/37.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 37.56/37.80  thf(d10_xboole_0, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 37.56/37.80  thf('35', plain,
% 37.56/37.80      (![X10 : $i, X12 : $i]:
% 37.56/37.80         (((X10) = (X12))
% 37.56/37.80          | ~ (r1_tarski @ X12 @ X10)
% 37.56/37.80          | ~ (r1_tarski @ X10 @ X12))),
% 37.56/37.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.56/37.80  thf('36', plain,
% 37.56/37.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['34', '35'])).
% 37.56/37.80  thf('37', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((X1) = (X0))
% 37.56/37.80          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 37.56/37.80              = (k1_xboole_0)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['33', '36'])).
% 37.56/37.80  thf('38', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 37.56/37.80            = (k1_xboole_0))
% 37.56/37.80          | ((X0) = (X1)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['10', '37'])).
% 37.56/37.80  thf('39', plain,
% 37.56/37.80      (![X21 : $i, X22 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 37.56/37.80           = (k3_xboole_0 @ X21 @ X22))),
% 37.56/37.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 37.56/37.80  thf('40', plain,
% 37.56/37.80      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 37.56/37.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 37.56/37.80  thf(l32_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 37.56/37.80  thf('41', plain,
% 37.56/37.80      (![X13 : $i, X15 : $i]:
% 37.56/37.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 37.56/37.80          | ~ (r1_tarski @ X13 @ X15))),
% 37.56/37.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 37.56/37.80  thf('42', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['40', '41'])).
% 37.56/37.80  thf('43', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['39', '42'])).
% 37.56/37.80  thf('44', plain,
% 37.56/37.80      (![X21 : $i, X22 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 37.56/37.80           = (k3_xboole_0 @ X21 @ X22))),
% 37.56/37.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 37.56/37.80  thf('45', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 37.56/37.80           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['43', '44'])).
% 37.56/37.80  thf('46', plain,
% 37.56/37.80      (![X21 : $i, X22 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 37.56/37.80           = (k3_xboole_0 @ X21 @ X22))),
% 37.56/37.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 37.56/37.80  thf('47', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 37.56/37.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 37.56/37.80  thf('48', plain,
% 37.56/37.80      (![X13 : $i, X15 : $i]:
% 37.56/37.80         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 37.56/37.80          | ~ (r1_tarski @ X13 @ X15))),
% 37.56/37.80      inference('cnf', [status(esa)], [l32_xboole_1])).
% 37.56/37.80  thf('49', plain,
% 37.56/37.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['47', '48'])).
% 37.56/37.80  thf('50', plain,
% 37.56/37.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['46', '49'])).
% 37.56/37.80  thf('51', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 37.56/37.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 37.56/37.80  thf('52', plain,
% 37.56/37.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['50', '51'])).
% 37.56/37.80  thf(t100_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 37.56/37.80  thf('53', plain,
% 37.56/37.80      (![X16 : $i, X17 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X16 @ X17)
% 37.56/37.80           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 37.56/37.80  thf('54', plain,
% 37.56/37.80      (![X0 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['52', '53'])).
% 37.56/37.80  thf('55', plain,
% 37.56/37.80      (![X0 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['52', '53'])).
% 37.56/37.80  thf('56', plain,
% 37.56/37.80      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 37.56/37.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 37.56/37.80  thf('57', plain,
% 37.56/37.80      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 37.56/37.80      inference('sup+', [status(thm)], ['55', '56'])).
% 37.56/37.80  thf('58', plain,
% 37.56/37.80      (![X10 : $i, X12 : $i]:
% 37.56/37.80         (((X10) = (X12))
% 37.56/37.80          | ~ (r1_tarski @ X12 @ X10)
% 37.56/37.80          | ~ (r1_tarski @ X10 @ X12))),
% 37.56/37.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.56/37.80  thf('59', plain,
% 37.56/37.80      (![X0 : $i]:
% 37.56/37.80         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 37.56/37.80          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['57', '58'])).
% 37.56/37.80  thf('60', plain,
% 37.56/37.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 37.56/37.80      inference('sup-', [status(thm)], ['47', '48'])).
% 37.56/37.80  thf(t98_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]:
% 37.56/37.80     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 37.56/37.80  thf('61', plain,
% 37.56/37.80      (![X25 : $i, X26 : $i]:
% 37.56/37.80         ((k2_xboole_0 @ X25 @ X26)
% 37.56/37.80           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 37.56/37.80  thf('62', plain,
% 37.56/37.80      (![X0 : $i]:
% 37.56/37.80         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['60', '61'])).
% 37.56/37.80  thf(t7_xboole_1, axiom,
% 37.56/37.80    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 37.56/37.80  thf('63', plain,
% 37.56/37.80      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 37.56/37.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 37.56/37.80  thf('64', plain,
% 37.56/37.80      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['62', '63'])).
% 37.56/37.80  thf('65', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 37.56/37.80      inference('demod', [status(thm)], ['59', '64'])).
% 37.56/37.80  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 37.56/37.80      inference('demod', [status(thm)], ['54', '65'])).
% 37.56/37.80  thf('67', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 37.56/37.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 37.56/37.80  thf('68', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k3_xboole_0 @ X0 @ X1)
% 37.56/37.80           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 37.56/37.80      inference('demod', [status(thm)], ['45', '66', '67'])).
% 37.56/37.80  thf('69', plain,
% 37.56/37.80      (![X16 : $i, X17 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X16 @ X17)
% 37.56/37.80           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 37.56/37.80  thf('70', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 37.56/37.80           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['68', '69'])).
% 37.56/37.80  thf('71', plain,
% 37.56/37.80      (![X16 : $i, X17 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X16 @ X17)
% 37.56/37.80           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 37.56/37.80  thf('72', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 37.56/37.80           = (k4_xboole_0 @ X1 @ X0))),
% 37.56/37.80      inference('demod', [status(thm)], ['70', '71'])).
% 37.56/37.80  thf('73', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ k1_xboole_0)
% 37.56/37.80            = (k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))
% 37.56/37.80          | ((X1) = (X0)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['38', '72'])).
% 37.56/37.80  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 37.56/37.80      inference('demod', [status(thm)], ['54', '65'])).
% 37.56/37.80  thf('75', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k2_tarski @ X1 @ X1)
% 37.56/37.80            = (k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))
% 37.56/37.80          | ((X1) = (X0)))),
% 37.56/37.80      inference('demod', [status(thm)], ['73', '74'])).
% 37.56/37.80  thf('76', plain,
% 37.56/37.80      (![X25 : $i, X26 : $i]:
% 37.56/37.80         ((k2_xboole_0 @ X25 @ X26)
% 37.56/37.80           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t98_xboole_1])).
% 37.56/37.80  thf('77', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 37.56/37.80            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 37.56/37.80          | ((X0) = (X1)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['75', '76'])).
% 37.56/37.80  thf('78', plain,
% 37.56/37.80      (![X32 : $i, X33 : $i, X34 : $i]:
% 37.56/37.80         ((k1_enumset1 @ X32 @ X33 @ X34)
% 37.56/37.80           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 37.56/37.80      inference('cnf', [status(esa)], [t42_enumset1])).
% 37.56/37.80  thf('79', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k1_enumset1 @ X1 @ X0 @ X0)
% 37.56/37.80            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 37.56/37.80          | ((X0) = (X1)))),
% 37.56/37.80      inference('demod', [status(thm)], ['77', '78'])).
% 37.56/37.80  thf('80', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))
% 37.56/37.80          | ((X1) = (X0))
% 37.56/37.80          | ((X0) = (X1)))),
% 37.56/37.80      inference('sup+', [status(thm)], ['9', '79'])).
% 37.56/37.80  thf('81', plain,
% 37.56/37.80      (![X0 : $i, X1 : $i]:
% 37.56/37.80         (((X1) = (X0))
% 37.56/37.80          | ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0)))),
% 37.56/37.80      inference('simplify', [status(thm)], ['80'])).
% 37.56/37.80  thf('82', plain,
% 37.56/37.80      (((k1_enumset1 @ sk_A @ sk_B @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 37.56/37.80      inference('demod', [status(thm)], ['2', '5'])).
% 37.56/37.80  thf('83', plain,
% 37.56/37.80      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 37.56/37.80        | ((sk_A) = (sk_B)))),
% 37.56/37.80      inference('sup-', [status(thm)], ['81', '82'])).
% 37.56/37.80  thf('84', plain, (((sk_A) = (sk_B))),
% 37.56/37.80      inference('simplify', [status(thm)], ['83'])).
% 37.56/37.80  thf('85', plain, (((sk_A) = (sk_B))),
% 37.56/37.80      inference('simplify', [status(thm)], ['83'])).
% 37.56/37.80  thf(t70_enumset1, axiom,
% 37.56/37.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 37.56/37.80  thf('86', plain,
% 37.56/37.80      (![X36 : $i, X37 : $i]:
% 37.56/37.80         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 37.56/37.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.56/37.80  thf('87', plain,
% 37.56/37.80      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 37.56/37.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.56/37.80  thf('88', plain,
% 37.56/37.80      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 37.56/37.80      inference('sup+', [status(thm)], ['86', '87'])).
% 37.56/37.80  thf('89', plain, (((sk_A) = (sk_B))),
% 37.56/37.80      inference('simplify', [status(thm)], ['83'])).
% 37.56/37.80  thf('90', plain,
% 37.56/37.80      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 37.56/37.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.56/37.80  thf('91', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 37.56/37.80      inference('demod', [status(thm)], ['6', '84', '85', '88', '89', '90'])).
% 37.56/37.80  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 37.56/37.80  
% 37.56/37.80  % SZS output end Refutation
% 37.56/37.80  
% 37.56/37.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
