%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2MzdzMQIH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 167 expanded)
%              Number of leaves         :   34 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  660 (1057 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( X10
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X10 @ X7 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X25: $i] :
      ( r1_tarski @ k1_xboole_0 @ X25 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,
    ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ ( k1_tarski @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','53'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X28 @ X29 ) @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('58',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('66',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','70'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('75',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('78',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K2MzdzMQIH
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 712 iterations in 0.344s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.80  thf(t46_zfmisc_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r2_hidden @ A @ B ) =>
% 0.59/0.80       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ( r2_hidden @ A @ B ) =>
% 0.59/0.80          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.59/0.80  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(l1_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X42 : $i, X44 : $i]:
% 0.59/0.80         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.59/0.80      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.59/0.80  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.59/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.80  thf(t28_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X23 : $i, X24 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.80  thf(t100_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X20 @ X21)
% 0.59/0.80           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.59/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.80  thf(t3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf(t1_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.80  thf('8', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf(d4_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.59/0.80       ( ![D:$i]:
% 0.59/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.80           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i, X10 : $i]:
% 0.59/0.80         (((X10) = (k3_xboole_0 @ X6 @ X7))
% 0.59/0.80          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X7)
% 0.59/0.80          | (r2_hidden @ (sk_D @ X10 @ X7 @ X6) @ X10))),
% 0.59/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.59/0.80          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('eq_fact', [status(thm)], ['9'])).
% 0.59/0.80  thf(d1_xboole_0, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((X0) = (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.80  thf('13', plain, (![X25 : $i]: (r1_tarski @ k1_xboole_0 @ X25)),
% 0.59/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X23 : $i, X24 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.80  thf(t69_enumset1, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf(l51_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X45 : $i, X46 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.59/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('21', plain, (((k3_tarski @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['19', '20'])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k3_tarski @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.59/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['16', '21'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k1_xboole_0) = (k2_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X9 @ X8)
% 0.59/0.80          | (r2_hidden @ X9 @ X7)
% 0.59/0.80          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.59/0.80         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['26', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.80          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.80  thf(symmetry_r1_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X11 : $i, X12 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.59/0.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X1) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.80  thf(d10_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.80  thf('36', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.59/0.80      inference('simplify', [status(thm)], ['35'])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X42 : $i, X43 : $i]:
% 0.59/0.80         ((r2_hidden @ X42 @ X43) | ~ (r1_tarski @ (k1_tarski @ X42) @ X43))),
% 0.59/0.80      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.59/0.80  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X15 @ X13)
% 0.59/0.80          | ~ (r2_hidden @ X15 @ X16)
% 0.59/0.80          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ X1) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['34', '40'])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 0.59/0.80          | ~ (v1_xboole_0 @ X0)
% 0.59/0.80          | ~ (v1_xboole_0 @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['24', '41'])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.80      inference('condensation', [status(thm)], ['42'])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['8', '43'])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['26', '28'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.80  thf(antisymmetry_r2_hidden, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ k1_xboole_0)
% 0.59/0.80          | ~ (r2_hidden @ X0 @ (sk_B @ k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['47', '50'])).
% 0.59/0.80  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.80  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('demod', [status(thm)], ['44', '52'])).
% 0.59/0.80  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['7', '53'])).
% 0.59/0.80  thf(t88_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.80       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (![X28 : $i, X29 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ (k2_xboole_0 @ X28 @ X29) @ X29) = (X28))
% 0.59/0.80          | ~ (r1_xboole_0 @ X28 @ X29))),
% 0.59/0.80      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf(commutativity_k2_tarski, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      (![X30 : $i, X31 : $i]:
% 0.59/0.80         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (![X45 : $i, X46 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.59/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['57', '58'])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X45 : $i, X46 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.59/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.80  thf('61', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['59', '60'])).
% 0.59/0.80  thf('62', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['61', '62'])).
% 0.59/0.80  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['56', '63'])).
% 0.59/0.80  thf('65', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.59/0.80      inference('simplify', [status(thm)], ['35'])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (![X23 : $i, X24 : $i]:
% 0.59/0.80         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.59/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.80  thf('67', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.80  thf('68', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X20 @ X21)
% 0.59/0.80           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.80  thf('69', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.80  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['64', '69'])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['6', '70'])).
% 0.59/0.80  thf(t39_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('72', plain,
% 0.59/0.80      (![X26 : $i, X27 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26))
% 0.59/0.80           = (k2_xboole_0 @ X26 @ X27))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('73', plain,
% 0.59/0.80      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.59/0.80         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['71', '72'])).
% 0.59/0.80  thf('74', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('75', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['73', '74'])).
% 0.59/0.80  thf('76', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['59', '60'])).
% 0.59/0.80  thf('78', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.59/0.80      inference('demod', [status(thm)], ['76', '77'])).
% 0.59/0.80  thf('79', plain, ($false),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['75', '78'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
