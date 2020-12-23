%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.untjDNHwYW

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:03 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 144 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  571 ( 838 expanded)
%              Number of equality atoms :   45 (  73 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('41',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['36','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','52'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X30 ) @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','63'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('68',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.untjDNHwYW
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 1358 iterations in 0.646s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.10  thf(t46_zfmisc_1, conjecture,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r2_hidden @ A @ B ) =>
% 0.91/1.10       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i,B:$i]:
% 0.91/1.10        ( ( r2_hidden @ A @ B ) =>
% 0.91/1.10          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.91/1.10  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(l1_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X41 : $i, X43 : $i]:
% 0.91/1.10         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.91/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.10  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.91/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.10  thf(t28_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X23 : $i, X24 : $i]:
% 0.91/1.10         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.91/1.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf(t100_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i]:
% 0.91/1.10         ((k4_xboole_0 @ X20 @ X21)
% 0.91/1.10           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.91/1.10         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf(t3_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.10            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X41 : $i, X43 : $i]:
% 0.91/1.10         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.91/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ X0 @ X1)
% 0.91/1.10          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.10  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.10  thf(t1_boole, axiom,
% 0.91/1.10    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.10  thf('11', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.91/1.10      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.10  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf(t7_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.91/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.10  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.10      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf(d10_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X17 : $i, X19 : $i]:
% 0.91/1.10         (((X17) = (X19))
% 0.91/1.10          | ~ (r1_tarski @ X19 @ X17)
% 0.91/1.10          | ~ (r1_tarski @ X17 @ X19))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.10          | ((k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('19', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.91/1.10      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X41 : $i, X42 : $i]:
% 0.91/1.10         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 0.91/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.10  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf(d1_xboole_0, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf('23', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ k1_xboole_0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['17', '23'])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.10      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X23 : $i, X24 : $i]:
% 0.91/1.10         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.91/1.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.10  thf(d4_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.91/1.10       ( ![D:$i]:
% 0.91/1.10         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.10           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X11 @ X10)
% 0.91/1.10          | (r2_hidden @ X11 @ X9)
% 0.91/1.10          | ((X10) != (k3_xboole_0 @ X8 @ X9)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.91/1.10         ((r2_hidden @ X11 @ X9)
% 0.91/1.10          | ~ (r2_hidden @ X11 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['29'])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['28', '30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['25', '31'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf(antisymmetry_r2_hidden, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.91/1.10      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r2_hidden @ X0 @ (sk_B @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.10  thf('36', plain,
% 0.91/1.10      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (sk_B @ k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['32', '35'])).
% 0.91/1.10  thf('37', plain,
% 0.91/1.10      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf('38', plain,
% 0.91/1.10      (![X41 : $i, X43 : $i]:
% 0.91/1.10         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.91/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.10  thf('39', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.10  thf('41', plain,
% 0.91/1.10      (((v1_xboole_0 @ k1_xboole_0)
% 0.91/1.10        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.91/1.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.10  thf('44', plain,
% 0.91/1.10      (![X41 : $i, X42 : $i]:
% 0.91/1.10         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 0.91/1.10      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.10  thf('45', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.10  thf('47', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ~ (v1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['42', '47'])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.91/1.10          | (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['41', '48'])).
% 0.91/1.10  thf('50', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.91/1.10      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.10  thf('51', plain,
% 0.91/1.10      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.10  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.10      inference('clc', [status(thm)], ['36', '51'])).
% 0.91/1.10  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.10      inference('demod', [status(thm)], ['24', '52'])).
% 0.91/1.10  thf(t88_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r1_xboole_0 @ A @ B ) =>
% 0.91/1.10       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.91/1.10  thf('54', plain,
% 0.91/1.10      (![X29 : $i, X30 : $i]:
% 0.91/1.10         (((k4_xboole_0 @ (k2_xboole_0 @ X29 @ X30) @ X30) = (X29))
% 0.91/1.10          | ~ (r1_xboole_0 @ X29 @ X30))),
% 0.91/1.10      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.91/1.10  thf('55', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['53', '54'])).
% 0.91/1.10  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['55', '56'])).
% 0.91/1.10  thf('58', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.91/1.10      inference('simplify', [status(thm)], ['18'])).
% 0.91/1.10  thf('59', plain,
% 0.91/1.10      (![X23 : $i, X24 : $i]:
% 0.91/1.10         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.91/1.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.10  thf('60', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.10  thf('61', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i]:
% 0.91/1.10         ((k4_xboole_0 @ X20 @ X21)
% 0.91/1.10           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.10  thf('62', plain,
% 0.91/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['60', '61'])).
% 0.91/1.10  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['57', '62'])).
% 0.91/1.10  thf('64', plain,
% 0.91/1.10      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['6', '63'])).
% 0.91/1.10  thf(t39_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.10  thf('65', plain,
% 0.91/1.10      (![X25 : $i, X26 : $i]:
% 0.91/1.10         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.91/1.10           = (k2_xboole_0 @ X25 @ X26))),
% 0.91/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.10  thf('66', plain,
% 0.91/1.10      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.91/1.10         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['64', '65'])).
% 0.91/1.10  thf('67', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.91/1.10      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.10  thf('68', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.10  thf('69', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('70', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.10  thf('71', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['69', '70'])).
% 0.91/1.10  thf('72', plain, ($false),
% 0.91/1.10      inference('simplify_reflect-', [status(thm)], ['68', '71'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
