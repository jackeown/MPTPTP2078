%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FExtClix1R

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:15 EST 2020

% Result     : Theorem 28.10s
% Output     : Refutation 28.10s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 510 expanded)
%              Number of leaves         :   42 ( 184 expanded)
%              Depth                    :   17
%              Number of atoms          : 1704 (5695 expanded)
%              Number of equality atoms :  156 ( 492 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,
    ( sk_C
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('19',plain,(
    ! [X90: $i,X91: $i,X92: $i,X93: $i] :
      ( ( k3_enumset1 @ X90 @ X90 @ X91 @ X92 @ X93 )
      = ( k2_enumset1 @ X90 @ X91 @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X87: $i,X88: $i,X89: $i] :
      ( ( k2_enumset1 @ X87 @ X87 @ X88 @ X89 )
      = ( k1_enumset1 @ X87 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X15 @ X13 @ X14 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X22 @ X21 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('27',plain,(
    ! [X87: $i,X88: $i,X89: $i] :
      ( ( k2_enumset1 @ X87 @ X87 @ X88 @ X89 )
      = ( k1_enumset1 @ X87 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('32',plain,(
    ! [X99: $i,X100: $i,X101: $i,X102: $i,X103: $i,X104: $i] :
      ( ( k5_enumset1 @ X99 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104 )
      = ( k4_enumset1 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X19 @ X18 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X15 @ X13 @ X14 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X1 @ X0 @ X2 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X6 @ X3 @ X2 @ X0 @ X1 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X87: $i,X88: $i,X89: $i] :
      ( ( k2_enumset1 @ X87 @ X87 @ X88 @ X89 )
      = ( k1_enumset1 @ X87 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X90: $i,X91: $i,X92: $i,X93: $i] :
      ( ( k3_enumset1 @ X90 @ X90 @ X91 @ X92 @ X93 )
      = ( k2_enumset1 @ X90 @ X91 @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('52',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k6_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X52 @ X53 @ X54 ) @ ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('54',plain,(
    ! [X105: $i,X106: $i,X107: $i,X108: $i,X109: $i,X110: $i,X111: $i] :
      ( ( k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 )
      = ( k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','57'])).

thf('59',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','61'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('63',plain,(
    ! [X94: $i,X95: $i,X96: $i,X97: $i,X98: $i] :
      ( ( k4_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98 )
      = ( k3_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('64',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ( k6_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 ) @ ( k2_tarski @ X74 @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X105: $i,X106: $i,X107: $i,X108: $i,X109: $i,X110: $i,X111: $i] :
      ( ( k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 )
      = ( k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X15 @ X13 @ X14 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('69',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X22 @ X21 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('72',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X1 @ X5 @ X3 @ X4 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X1 @ X5 @ X3 @ X4 @ X2 )
      = ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','67','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X112: $i,X113: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X112 @ X113 ) )
      = ( k2_xboole_0 @ X112 @ X113 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X112: $i,X113: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X112 @ X113 ) )
      = ( k2_xboole_0 @ X112 @ X113 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','84'])).

thf('86',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_C )
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('90',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['85','90'])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('95',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('96',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','91','92','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('116',plain,(
    ! [X85: $i,X86: $i] :
      ( ( k1_enumset1 @ X85 @ X85 @ X86 )
      = ( k2_tarski @ X85 @ X86 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X94: $i,X95: $i,X96: $i,X97: $i,X98: $i] :
      ( ( k4_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98 )
      = ( k3_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('119',plain,(
    ! [X99: $i,X100: $i,X101: $i,X102: $i,X103: $i,X104: $i] :
      ( ( k5_enumset1 @ X99 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104 )
      = ( k4_enumset1 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('120',plain,(
    ! [X84: $i] :
      ( ( k2_tarski @ X84 @ X84 )
      = ( k1_tarski @ X84 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('121',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_xboole_0 @ ( k2_tarski @ X44 @ X45 ) @ ( k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X105: $i,X106: $i,X107: $i,X108: $i,X109: $i,X110: $i,X111: $i] :
      ( ( k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 )
      = ( k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('125',plain,(
    ! [X114: $i,X115: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X114 ) @ X115 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','128'])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FExtClix1R
% 0.16/0.36  % Computer   : n014.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 13:03:37 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 28.10/28.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.10/28.36  % Solved by: fo/fo7.sh
% 28.10/28.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.10/28.36  % done 10837 iterations in 27.915s
% 28.10/28.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.10/28.36  % SZS output start Refutation
% 28.10/28.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 28.10/28.36  thf(sk_B_type, type, sk_B: $i).
% 28.10/28.36  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 28.10/28.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 28.10/28.36  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 28.10/28.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.10/28.36  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 28.10/28.36  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 28.10/28.36  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 28.10/28.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 28.10/28.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 28.10/28.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 28.10/28.36  thf(sk_C_type, type, sk_C: $i).
% 28.10/28.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 28.10/28.36  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 28.10/28.36                                           $i > $i).
% 28.10/28.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 28.10/28.36  thf(sk_A_type, type, sk_A: $i).
% 28.10/28.36  thf(t50_zfmisc_1, conjecture,
% 28.10/28.36    (![A:$i,B:$i,C:$i]:
% 28.10/28.36     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 28.10/28.36  thf(zf_stmt_0, negated_conjecture,
% 28.10/28.36    (~( ![A:$i,B:$i,C:$i]:
% 28.10/28.36        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 28.10/28.36    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 28.10/28.36  thf('0', plain,
% 28.10/28.36      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 28.10/28.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.10/28.36  thf(t95_xboole_1, axiom,
% 28.10/28.36    (![A:$i,B:$i]:
% 28.10/28.36     ( ( k3_xboole_0 @ A @ B ) =
% 28.10/28.36       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 28.10/28.36  thf('1', plain,
% 28.10/28.36      (![X11 : $i, X12 : $i]:
% 28.10/28.36         ((k3_xboole_0 @ X11 @ X12)
% 28.10/28.36           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 28.10/28.36              (k2_xboole_0 @ X11 @ X12)))),
% 28.10/28.36      inference('cnf', [status(esa)], [t95_xboole_1])).
% 28.10/28.36  thf('2', plain,
% 28.10/28.36      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 28.10/28.36         = (k5_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 28.10/28.36            k1_xboole_0))),
% 28.10/28.36      inference('sup+', [status(thm)], ['0', '1'])).
% 28.10/28.36  thf(t5_boole, axiom,
% 28.10/28.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 28.10/28.36  thf('3', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 28.10/28.36      inference('cnf', [status(esa)], [t5_boole])).
% 28.10/28.36  thf('4', plain,
% 28.10/28.36      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 28.10/28.36         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 28.10/28.36      inference('demod', [status(thm)], ['2', '3'])).
% 28.10/28.36  thf(t92_xboole_1, axiom,
% 28.10/28.36    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 28.10/28.36  thf('5', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 28.10/28.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 28.10/28.36  thf(t91_xboole_1, axiom,
% 28.10/28.36    (![A:$i,B:$i,C:$i]:
% 28.10/28.36     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 28.10/28.36       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 28.10/28.36  thf('6', plain,
% 28.10/28.36      (![X7 : $i, X8 : $i, X9 : $i]:
% 28.10/28.36         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 28.10/28.36           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 28.10/28.36      inference('cnf', [status(esa)], [t91_xboole_1])).
% 28.10/28.36  thf('7', plain,
% 28.10/28.36      (![X0 : $i, X1 : $i]:
% 28.10/28.36         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 28.10/28.36           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 28.10/28.36      inference('sup+', [status(thm)], ['5', '6'])).
% 28.10/28.36  thf('8', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 28.10/28.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 28.10/28.36  thf('9', plain,
% 28.10/28.36      (![X11 : $i, X12 : $i]:
% 28.10/28.36         ((k3_xboole_0 @ X11 @ X12)
% 28.10/28.36           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 28.10/28.36              (k2_xboole_0 @ X11 @ X12)))),
% 28.10/28.36      inference('cnf', [status(esa)], [t95_xboole_1])).
% 28.10/28.36  thf('10', plain,
% 28.10/28.36      (![X0 : $i]:
% 28.10/28.36         ((k3_xboole_0 @ X0 @ X0)
% 28.10/28.36           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 28.10/28.36      inference('sup+', [status(thm)], ['8', '9'])).
% 28.10/28.36  thf(idempotence_k3_xboole_0, axiom,
% 28.10/28.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 28.10/28.36  thf('11', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 28.10/28.36      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 28.10/28.36  thf(idempotence_k2_xboole_0, axiom,
% 28.10/28.36    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 28.10/28.36  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 28.10/28.36      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 28.10/28.36  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 28.10/28.36      inference('demod', [status(thm)], ['10', '11', '12'])).
% 28.10/28.36  thf('14', plain,
% 28.10/28.36      (![X0 : $i, X1 : $i]:
% 28.10/28.36         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 28.10/28.36      inference('demod', [status(thm)], ['7', '13'])).
% 28.10/28.36  thf('15', plain,
% 28.10/28.36      (((sk_C)
% 28.10/28.36         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 28.10/28.36            (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 28.10/28.36      inference('sup+', [status(thm)], ['4', '14'])).
% 28.10/28.36  thf(t100_xboole_1, axiom,
% 28.10/28.36    (![A:$i,B:$i]:
% 28.10/28.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 28.10/28.37  thf('16', plain,
% 28.10/28.37      (![X2 : $i, X3 : $i]:
% 28.10/28.37         ((k4_xboole_0 @ X2 @ X3)
% 28.10/28.37           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 28.10/28.37  thf('17', plain,
% 28.10/28.37      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 28.10/28.37      inference('demod', [status(thm)], ['15', '16'])).
% 28.10/28.37  thf('18', plain,
% 28.10/28.37      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 28.10/28.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.10/28.37  thf(t72_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i]:
% 28.10/28.37     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 28.10/28.37  thf('19', plain,
% 28.10/28.37      (![X90 : $i, X91 : $i, X92 : $i, X93 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X90 @ X90 @ X91 @ X92 @ X93)
% 28.10/28.37           = (k2_enumset1 @ X90 @ X91 @ X92 @ X93))),
% 28.10/28.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 28.10/28.37  thf(t71_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i]:
% 28.10/28.37     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 28.10/28.37  thf('20', plain,
% 28.10/28.37      (![X87 : $i, X88 : $i, X89 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X87 @ X87 @ X88 @ X89)
% 28.10/28.37           = (k1_enumset1 @ X87 @ X88 @ X89))),
% 28.10/28.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 28.10/28.37  thf('21', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['19', '20'])).
% 28.10/28.37  thf(t100_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i]:
% 28.10/28.37     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 28.10/28.37  thf('22', plain,
% 28.10/28.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X15 @ X13 @ X14) = (k1_enumset1 @ X13 @ X14 @ X15))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_enumset1])).
% 28.10/28.37  thf(t70_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 28.10/28.37  thf('23', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf('24', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['22', '23'])).
% 28.10/28.37  thf('25', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['21', '24'])).
% 28.10/28.37  thf(t104_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i]:
% 28.10/28.37     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 28.10/28.37  thf('26', plain,
% 28.10/28.37      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X20 @ X22 @ X21 @ X23)
% 28.10/28.37           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 28.10/28.37      inference('cnf', [status(esa)], [t104_enumset1])).
% 28.10/28.37  thf('27', plain,
% 28.10/28.37      (![X87 : $i, X88 : $i, X89 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X87 @ X87 @ X88 @ X89)
% 28.10/28.37           = (k1_enumset1 @ X87 @ X88 @ X89))),
% 28.10/28.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 28.10/28.37  thf('28', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['26', '27'])).
% 28.10/28.37  thf('29', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf(t58_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 28.10/28.37     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 28.10/28.37       ( k2_xboole_0 @
% 28.10/28.37         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 28.10/28.37  thf('30', plain,
% 28.10/28.37      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ 
% 28.10/28.37              (k2_enumset1 @ X33 @ X34 @ X35 @ X36)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t58_enumset1])).
% 28.10/28.37  thf('31', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['29', '30'])).
% 28.10/28.37  thf(t74_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 28.10/28.37     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 28.10/28.37       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 28.10/28.37  thf('32', plain,
% 28.10/28.37      (![X99 : $i, X100 : $i, X101 : $i, X102 : $i, X103 : $i, X104 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X99 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104)
% 28.10/28.37           = (k4_enumset1 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104))),
% 28.10/28.37      inference('cnf', [status(esa)], [t74_enumset1])).
% 28.10/28.37  thf('33', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('demod', [status(thm)], ['31', '32'])).
% 28.10/28.37  thf('34', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X2 @ X0)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 28.10/28.37              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['28', '33'])).
% 28.10/28.37  thf(t103_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i]:
% 28.10/28.37     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 28.10/28.37  thf('35', plain,
% 28.10/28.37      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X16 @ X17 @ X19 @ X18)
% 28.10/28.37           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 28.10/28.37      inference('cnf', [status(esa)], [t103_enumset1])).
% 28.10/28.37  thf('36', plain,
% 28.10/28.37      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ 
% 28.10/28.37              (k2_enumset1 @ X33 @ X34 @ X35 @ X36)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t58_enumset1])).
% 28.10/28.37  thf('37', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 28.10/28.37              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['35', '36'])).
% 28.10/28.37  thf('38', plain,
% 28.10/28.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X15 @ X13 @ X14) = (k1_enumset1 @ X13 @ X14 @ X15))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_enumset1])).
% 28.10/28.37  thf('39', plain,
% 28.10/28.37      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ 
% 28.10/28.37              (k2_enumset1 @ X33 @ X34 @ X35 @ X36)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t58_enumset1])).
% 28.10/28.37  thf('40', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X1 @ X0 @ X2 @ X6 @ X5 @ X4 @ X3)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['38', '39'])).
% 28.10/28.37  thf('41', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X5 @ X4 @ X6 @ X3 @ X2 @ X0 @ X1)
% 28.10/28.37           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['37', '40'])).
% 28.10/28.37  thf('42', plain,
% 28.10/28.37      (![X87 : $i, X88 : $i, X89 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X87 @ X87 @ X88 @ X89)
% 28.10/28.37           = (k1_enumset1 @ X87 @ X88 @ X89))),
% 28.10/28.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 28.10/28.37  thf('43', plain,
% 28.10/28.37      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ 
% 28.10/28.37              (k2_enumset1 @ X33 @ X34 @ X35 @ X36)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t58_enumset1])).
% 28.10/28.37  thf('44', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 28.10/28.37              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['42', '43'])).
% 28.10/28.37  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 28.10/28.37      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 28.10/28.37  thf('46', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X2 @ X1 @ X0 @ X2 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['44', '45'])).
% 28.10/28.37  thf('47', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X0 @ X1 @ X2 @ X2 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['41', '46'])).
% 28.10/28.37  thf('48', plain,
% 28.10/28.37      (![X90 : $i, X91 : $i, X92 : $i, X93 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X90 @ X90 @ X91 @ X92 @ X93)
% 28.10/28.37           = (k2_enumset1 @ X90 @ X91 @ X92 @ X93))),
% 28.10/28.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 28.10/28.37  thf('49', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('demod', [status(thm)], ['31', '32'])).
% 28.10/28.37  thf('50', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 28.10/28.37              (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['48', '49'])).
% 28.10/28.37  thf('51', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf(t64_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 28.10/28.37     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 28.10/28.37       ( k2_xboole_0 @
% 28.10/28.37         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 28.10/28.37  thf('52', plain,
% 28.10/28.37      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, 
% 28.10/28.37         X59 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X52 @ X53 @ X54) @ 
% 28.10/28.37              (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t64_enumset1])).
% 28.10/28.37  thf('53', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['51', '52'])).
% 28.10/28.37  thf(t75_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 28.10/28.37     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 28.10/28.37       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 28.10/28.37  thf('54', plain,
% 28.10/28.37      (![X105 : $i, X106 : $i, X107 : $i, X108 : $i, X109 : $i, X110 : $i, 
% 28.10/28.37         X111 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111)
% 28.10/28.37           = (k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111))),
% 28.10/28.37      inference('cnf', [status(esa)], [t75_enumset1])).
% 28.10/28.37  thf('55', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('demod', [status(thm)], ['53', '54'])).
% 28.10/28.37  thf('56', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['50', '55'])).
% 28.10/28.37  thf('57', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 28.10/28.37      inference('demod', [status(thm)], ['47', '56'])).
% 28.10/28.37  thf('58', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 28.10/28.37           = (k1_enumset1 @ X1 @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['34', '57'])).
% 28.10/28.37  thf('59', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf('60', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['22', '23'])).
% 28.10/28.37  thf('61', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))
% 28.10/28.37           = (k2_tarski @ X1 @ X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['58', '59', '60'])).
% 28.10/28.37  thf('62', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ (k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X0) @ 
% 28.10/28.37           (k2_tarski @ X1 @ X0)) = (k2_tarski @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['25', '61'])).
% 28.10/28.37  thf(t73_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 28.10/28.37     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 28.10/28.37       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 28.10/28.37  thf('63', plain,
% 28.10/28.37      (![X94 : $i, X95 : $i, X96 : $i, X97 : $i, X98 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98)
% 28.10/28.37           = (k3_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98))),
% 28.10/28.37      inference('cnf', [status(esa)], [t73_enumset1])).
% 28.10/28.37  thf(t67_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 28.10/28.37     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 28.10/28.37       ( k2_xboole_0 @
% 28.10/28.37         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 28.10/28.37  thf('64', plain,
% 28.10/28.37      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, 
% 28.10/28.37         X75 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 @ X75)
% 28.10/28.37           = (k2_xboole_0 @ 
% 28.10/28.37              (k4_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73) @ 
% 28.10/28.37              (k2_tarski @ X74 @ X75)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t67_enumset1])).
% 28.10/28.37  thf('65', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 28.10/28.37           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 28.10/28.37              (k2_tarski @ X6 @ X5)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['63', '64'])).
% 28.10/28.37  thf('66', plain,
% 28.10/28.37      (![X105 : $i, X106 : $i, X107 : $i, X108 : $i, X109 : $i, X110 : $i, 
% 28.10/28.37         X111 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111)
% 28.10/28.37           = (k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111))),
% 28.10/28.37      inference('cnf', [status(esa)], [t75_enumset1])).
% 28.10/28.37  thf('67', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 28.10/28.37           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 28.10/28.37              (k2_tarski @ X6 @ X5)))),
% 28.10/28.37      inference('demod', [status(thm)], ['65', '66'])).
% 28.10/28.37  thf('68', plain,
% 28.10/28.37      (![X13 : $i, X14 : $i, X15 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X15 @ X13 @ X14) = (k1_enumset1 @ X13 @ X14 @ X15))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_enumset1])).
% 28.10/28.37  thf('69', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf('70', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['68', '69'])).
% 28.10/28.37  thf('71', plain,
% 28.10/28.37      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 28.10/28.37         ((k2_enumset1 @ X20 @ X22 @ X21 @ X23)
% 28.10/28.37           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 28.10/28.37      inference('cnf', [status(esa)], [t104_enumset1])).
% 28.10/28.37  thf('72', plain,
% 28.10/28.37      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ 
% 28.10/28.37              (k2_enumset1 @ X33 @ X34 @ X35 @ X36)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t58_enumset1])).
% 28.10/28.37  thf('73', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0)
% 28.10/28.37           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 28.10/28.37              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['71', '72'])).
% 28.10/28.37  thf('74', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X0 @ X1 @ X1 @ X5 @ X3 @ X4 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['70', '73'])).
% 28.10/28.37  thf('75', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 28.10/28.37              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 28.10/28.37      inference('demod', [status(thm)], ['31', '32'])).
% 28.10/28.37  thf('76', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X0 @ X1 @ X1 @ X5 @ X3 @ X4 @ X2)
% 28.10/28.37           = (k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2))),
% 28.10/28.37      inference('demod', [status(thm)], ['74', '75'])).
% 28.10/28.37  thf('77', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X1 @ X0)
% 28.10/28.37           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 28.10/28.37      inference('demod', [status(thm)], ['47', '56'])).
% 28.10/28.37  thf('78', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['62', '67', '76', '77'])).
% 28.10/28.37  thf('79', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['68', '69'])).
% 28.10/28.37  thf('80', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['78', '79'])).
% 28.10/28.37  thf(l51_zfmisc_1, axiom,
% 28.10/28.37    (![A:$i,B:$i]:
% 28.10/28.37     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 28.10/28.37  thf('81', plain,
% 28.10/28.37      (![X112 : $i, X113 : $i]:
% 28.10/28.37         ((k3_tarski @ (k2_tarski @ X112 @ X113)) = (k2_xboole_0 @ X112 @ X113))),
% 28.10/28.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 28.10/28.37  thf('82', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['80', '81'])).
% 28.10/28.37  thf('83', plain,
% 28.10/28.37      (![X112 : $i, X113 : $i]:
% 28.10/28.37         ((k3_tarski @ (k2_tarski @ X112 @ X113)) = (k2_xboole_0 @ X112 @ X113))),
% 28.10/28.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 28.10/28.37  thf('84', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 28.10/28.37      inference('sup+', [status(thm)], ['82', '83'])).
% 28.10/28.37  thf('85', plain,
% 28.10/28.37      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 28.10/28.37      inference('demod', [status(thm)], ['18', '84'])).
% 28.10/28.37  thf('86', plain,
% 28.10/28.37      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 28.10/28.37      inference('demod', [status(thm)], ['15', '16'])).
% 28.10/28.37  thf(t39_xboole_1, axiom,
% 28.10/28.37    (![A:$i,B:$i]:
% 28.10/28.37     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 28.10/28.37  thf('87', plain,
% 28.10/28.37      (![X4 : $i, X5 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 28.10/28.37           = (k2_xboole_0 @ X4 @ X5))),
% 28.10/28.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 28.10/28.37  thf('88', plain,
% 28.10/28.37      (((k2_xboole_0 @ sk_C @ sk_C)
% 28.10/28.37         = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['86', '87'])).
% 28.10/28.37  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 28.10/28.37      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 28.10/28.37  thf('90', plain,
% 28.10/28.37      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 28.10/28.37      inference('demod', [status(thm)], ['88', '89'])).
% 28.10/28.37  thf('91', plain, (((sk_C) = (k1_xboole_0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['85', '90'])).
% 28.10/28.37  thf('92', plain, (((sk_C) = (k1_xboole_0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['85', '90'])).
% 28.10/28.37  thf('93', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['10', '11', '12'])).
% 28.10/28.37  thf('94', plain,
% 28.10/28.37      (![X11 : $i, X12 : $i]:
% 28.10/28.37         ((k3_xboole_0 @ X11 @ X12)
% 28.10/28.37           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 28.10/28.37              (k2_xboole_0 @ X11 @ X12)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t95_xboole_1])).
% 28.10/28.37  thf('95', plain,
% 28.10/28.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 28.10/28.37         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 28.10/28.37           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t91_xboole_1])).
% 28.10/28.37  thf('96', plain,
% 28.10/28.37      (![X11 : $i, X12 : $i]:
% 28.10/28.37         ((k3_xboole_0 @ X11 @ X12)
% 28.10/28.37           = (k5_xboole_0 @ X11 @ 
% 28.10/28.37              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 28.10/28.37      inference('demod', [status(thm)], ['94', '95'])).
% 28.10/28.37  thf('97', plain,
% 28.10/28.37      (![X0 : $i]:
% 28.10/28.37         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 28.10/28.37           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['93', '96'])).
% 28.10/28.37  thf('98', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 28.10/28.37      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 28.10/28.37  thf('99', plain,
% 28.10/28.37      (![X2 : $i, X3 : $i]:
% 28.10/28.37         ((k4_xboole_0 @ X2 @ X3)
% 28.10/28.37           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 28.10/28.37  thf('100', plain,
% 28.10/28.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['98', '99'])).
% 28.10/28.37  thf('101', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 28.10/28.37      inference('cnf', [status(esa)], [t92_xboole_1])).
% 28.10/28.37  thf('102', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['100', '101'])).
% 28.10/28.37  thf('103', plain,
% 28.10/28.37      (![X4 : $i, X5 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 28.10/28.37           = (k2_xboole_0 @ X4 @ X5))),
% 28.10/28.37      inference('cnf', [status(esa)], [t39_xboole_1])).
% 28.10/28.37  thf('104', plain,
% 28.10/28.37      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['102', '103'])).
% 28.10/28.37  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 28.10/28.37      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 28.10/28.37  thf('106', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['104', '105'])).
% 28.10/28.37  thf('107', plain,
% 28.10/28.37      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 28.10/28.37      inference('demod', [status(thm)], ['97', '106'])).
% 28.10/28.37  thf('108', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 28.10/28.37      inference('cnf', [status(esa)], [t92_xboole_1])).
% 28.10/28.37  thf('109', plain,
% 28.10/28.37      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['107', '108'])).
% 28.10/28.37  thf('110', plain,
% 28.10/28.37      (![X2 : $i, X3 : $i]:
% 28.10/28.37         ((k4_xboole_0 @ X2 @ X3)
% 28.10/28.37           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 28.10/28.37  thf('111', plain,
% 28.10/28.37      (![X0 : $i]:
% 28.10/28.37         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['109', '110'])).
% 28.10/28.37  thf('112', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 28.10/28.37      inference('cnf', [status(esa)], [t5_boole])).
% 28.10/28.37  thf('113', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['111', '112'])).
% 28.10/28.37  thf('114', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 28.10/28.37      inference('demod', [status(thm)], ['17', '91', '92', '113'])).
% 28.10/28.37  thf('115', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['19', '20'])).
% 28.10/28.37  thf('116', plain,
% 28.10/28.37      (![X85 : $i, X86 : $i]:
% 28.10/28.37         ((k1_enumset1 @ X85 @ X85 @ X86) = (k2_tarski @ X85 @ X86))),
% 28.10/28.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 28.10/28.37  thf('117', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 28.10/28.37      inference('sup+', [status(thm)], ['115', '116'])).
% 28.10/28.37  thf('118', plain,
% 28.10/28.37      (![X94 : $i, X95 : $i, X96 : $i, X97 : $i, X98 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98)
% 28.10/28.37           = (k3_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98))),
% 28.10/28.37      inference('cnf', [status(esa)], [t73_enumset1])).
% 28.10/28.37  thf('119', plain,
% 28.10/28.37      (![X99 : $i, X100 : $i, X101 : $i, X102 : $i, X103 : $i, X104 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X99 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104)
% 28.10/28.37           = (k4_enumset1 @ X99 @ X100 @ X101 @ X102 @ X103 @ X104))),
% 28.10/28.37      inference('cnf', [status(esa)], [t74_enumset1])).
% 28.10/28.37  thf(t69_enumset1, axiom,
% 28.10/28.37    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 28.10/28.37  thf('120', plain,
% 28.10/28.37      (![X84 : $i]: ((k2_tarski @ X84 @ X84) = (k1_tarski @ X84))),
% 28.10/28.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 28.10/28.37  thf(t63_enumset1, axiom,
% 28.10/28.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 28.10/28.37     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 28.10/28.37       ( k2_xboole_0 @
% 28.10/28.37         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 28.10/28.37  thf('121', plain,
% 28.10/28.37      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 28.10/28.37         X51 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 28.10/28.37           = (k2_xboole_0 @ (k2_tarski @ X44 @ X45) @ 
% 28.10/28.37              (k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)))),
% 28.10/28.37      inference('cnf', [status(esa)], [t63_enumset1])).
% 28.10/28.37  thf('122', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)
% 28.10/28.37           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 28.10/28.37              (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 28.10/28.37      inference('sup+', [status(thm)], ['120', '121'])).
% 28.10/28.37  thf('123', plain,
% 28.10/28.37      (![X105 : $i, X106 : $i, X107 : $i, X108 : $i, X109 : $i, X110 : $i, 
% 28.10/28.37         X111 : $i]:
% 28.10/28.37         ((k6_enumset1 @ X105 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111)
% 28.10/28.37           = (k5_enumset1 @ X105 @ X106 @ X107 @ X108 @ X109 @ X110 @ X111))),
% 28.10/28.37      inference('cnf', [status(esa)], [t75_enumset1])).
% 28.10/28.37  thf('124', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)
% 28.10/28.37           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 28.10/28.37              (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 28.10/28.37      inference('demod', [status(thm)], ['122', '123'])).
% 28.10/28.37  thf(t49_zfmisc_1, axiom,
% 28.10/28.37    (![A:$i,B:$i]:
% 28.10/28.37     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 28.10/28.37  thf('125', plain,
% 28.10/28.37      (![X114 : $i, X115 : $i]:
% 28.10/28.37         ((k2_xboole_0 @ (k1_tarski @ X114) @ X115) != (k1_xboole_0))),
% 28.10/28.37      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 28.10/28.37  thf('126', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 28.10/28.37         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 28.10/28.37      inference('sup-', [status(thm)], ['124', '125'])).
% 28.10/28.37  thf('127', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 28.10/28.37         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 28.10/28.37      inference('sup-', [status(thm)], ['119', '126'])).
% 28.10/28.37  thf('128', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 28.10/28.37         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 28.10/28.37      inference('sup-', [status(thm)], ['118', '127'])).
% 28.10/28.37  thf('129', plain,
% 28.10/28.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 28.10/28.37      inference('sup-', [status(thm)], ['117', '128'])).
% 28.10/28.37  thf('130', plain, ($false),
% 28.10/28.37      inference('simplify_reflect-', [status(thm)], ['114', '129'])).
% 28.10/28.37  
% 28.10/28.37  % SZS output end Refutation
% 28.10/28.37  
% 28.10/28.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
