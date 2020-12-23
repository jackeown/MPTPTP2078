%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQcvHKRyFa

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 232 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  596 (1643 expanded)
%              Number of equality atoms :   46 ( 127 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X47 ) @ X49 )
      | ~ ( r2_hidden @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ( X26 != X27 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X27: $i] :
      ( r1_tarski @ X27 @ X27 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X34: $i] :
      ( r1_xboole_0 @ X34 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k3_xboole_0 @ X22 @ X25 ) )
      | ~ ( r1_xboole_0 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X26: $i,X28: $i] :
      ( ( X26 = X28 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','30'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','56'])).

thf('58',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X31: $i] :
      ( ( k2_xboole_0 @ X31 @ k1_xboole_0 )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['33','63'])).

thf('65',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SQcvHKRyFa
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 335 iterations in 0.142s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf(t46_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.57       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]:
% 0.21/0.57        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.57          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.21/0.57  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(l1_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X47 : $i, X49 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X47) @ X49) | ~ (r2_hidden @ X47 @ X49))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(t28_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_tarski @ X32 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf(t100_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X29 @ X30)
% 0.21/0.57           = (k5_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.57         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X26 : $i, X27 : $i]: ((r1_tarski @ X26 @ X27) | ((X26) != (X27)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('9', plain, (![X27 : $i]: (r1_tarski @ X27 @ X27)),
% 0.21/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_tarski @ X32 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X29 @ X30)
% 0.21/0.57           = (k5_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf(d5_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ X14)
% 0.21/0.57          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X16 @ X14)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.57          | (r2_hidden @ X16 @ X13)
% 0.21/0.57          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.57         ((r2_hidden @ X16 @ X13)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.21/0.57      inference('clc', [status(thm)], ['17', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '20'])).
% 0.21/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.57  thf('22', plain, (![X34 : $i]: (r1_xboole_0 @ X34 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf(t4_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X24 @ (k3_xboole_0 @ X22 @ X25))
% 0.21/0.57          | ~ (r1_xboole_0 @ X22 @ X25))),
% 0.21/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.57  thf('28', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X26 : $i, X28 : $i]:
% 0.21/0.57         (((X26) = (X28))
% 0.21/0.57          | ~ (r1_tarski @ X28 @ X26)
% 0.21/0.57          | ~ (r1_tarski @ X26 @ X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '30'])).
% 0.21/0.57  thf(t98_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X35 : $i, X36 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X35 @ X36)
% 0.21/0.57           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.57         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.57         ((r2_hidden @ X16 @ X13)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_tarski @ X32 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X29 @ X30)
% 0.21/0.57           = (k5_xboole_0 @ X29 @ (k3_xboole_0 @ X29 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf(t1_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X18 @ X19)
% 0.21/0.57          | ~ (r2_hidden @ X18 @ X20)
% 0.21/0.57          | ~ (r2_hidden @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.21/0.57          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.21/0.57          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.57         ((r2_hidden @ X16 @ X13)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['42', '56'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (![X35 : $i, X36 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X35 @ X36)
% 0.21/0.57           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1))
% 0.21/0.57           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf(t1_boole, axiom,
% 0.21/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.57  thf('61', plain, (![X31 : $i]: ((k2_xboole_0 @ X31 @ k1_xboole_0) = (X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.57  thf('63', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '62'])).
% 0.21/0.57  thf('64', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['33', '63'])).
% 0.21/0.57  thf('65', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf('67', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.57  thf('68', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
