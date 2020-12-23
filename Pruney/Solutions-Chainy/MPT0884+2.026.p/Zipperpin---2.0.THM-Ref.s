%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9kMcXrosod

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:26 EST 2020

% Result     : Theorem 21.53s
% Output     : Refutation 21.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 181 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  957 (2147 expanded)
%              Number of equality atoms :   67 ( 163 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t44_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('11',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','21'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X50 @ X52 @ X51 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k3_mcart_1 @ X63 @ X64 @ X65 )
      = ( k4_tarski @ ( k4_tarski @ X63 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('29',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k3_mcart_1 @ X63 @ X64 @ X65 )
      = ( k4_tarski @ ( k4_tarski @ X63 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X55 @ X58 ) @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X55 @ X56 ) @ ( k4_tarski @ X55 @ X57 ) @ ( k4_tarski @ X58 @ X56 ) @ ( k4_tarski @ X58 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k3_mcart_1 @ X63 @ X64 @ X65 )
      = ( k4_tarski @ ( k4_tarski @ X63 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k3_mcart_1 @ X63 @ X64 @ X65 )
      = ( k4_tarski @ ( k4_tarski @ X63 @ X64 ) @ X65 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X55 @ X58 ) @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X55 @ X56 ) @ ( k4_tarski @ X55 @ X57 ) @ ( k4_tarski @ X58 @ X56 ) @ ( k4_tarski @ X58 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('46',plain,(
    ! [X59: $i,X60: $i,X62: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X59 @ X60 ) @ ( k1_tarski @ X62 ) )
      = ( k2_tarski @ ( k4_tarski @ X59 @ X62 ) @ ( k4_tarski @ X60 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X0 ) )
      = ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('48',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k3_zfmisc_1 @ X66 @ X67 @ X68 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) @ X68 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('49',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['22','27','36','44','47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9kMcXrosod
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:54:40 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 21.53/21.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.53/21.72  % Solved by: fo/fo7.sh
% 21.53/21.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.53/21.72  % done 13293 iterations in 21.240s
% 21.53/21.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.53/21.72  % SZS output start Refutation
% 21.53/21.72  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 21.53/21.72  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 21.53/21.72  thf(sk_B_type, type, sk_B: $i).
% 21.53/21.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 21.53/21.72  thf(sk_C_type, type, sk_C: $i).
% 21.53/21.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 21.53/21.72  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 21.53/21.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 21.53/21.72  thf(sk_D_type, type, sk_D: $i).
% 21.53/21.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.53/21.72  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 21.53/21.72  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 21.53/21.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 21.53/21.72  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 21.53/21.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 21.53/21.72  thf(sk_A_type, type, sk_A: $i).
% 21.53/21.72  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 21.53/21.72                                           $i > $i).
% 21.53/21.72  thf(sk_E_type, type, sk_E: $i).
% 21.53/21.72  thf(t44_mcart_1, conjecture,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 21.53/21.72     ( ( k3_zfmisc_1 @
% 21.53/21.72         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 21.53/21.72       ( k2_enumset1 @
% 21.53/21.72         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 21.53/21.72         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 21.53/21.72  thf(zf_stmt_0, negated_conjecture,
% 21.53/21.72    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 21.53/21.72        ( ( k3_zfmisc_1 @
% 21.53/21.72            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 21.53/21.72          ( k2_enumset1 @
% 21.53/21.72            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 21.53/21.72            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 21.53/21.72    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 21.53/21.72  thf('0', plain,
% 21.53/21.72      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 21.53/21.72         (k2_tarski @ sk_D @ sk_E))
% 21.53/21.72         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 21.53/21.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.53/21.72  thf(t100_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 21.53/21.72  thf('1', plain,
% 21.53/21.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 21.53/21.72      inference('cnf', [status(esa)], [t100_enumset1])).
% 21.53/21.72  thf(t71_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 21.53/21.72  thf('2', plain,
% 21.53/21.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.53/21.72         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 21.53/21.72           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 21.53/21.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 21.53/21.72  thf(t70_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 21.53/21.72  thf('3', plain,
% 21.53/21.72      (![X23 : $i, X24 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 21.53/21.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 21.53/21.72  thf(t69_enumset1, axiom,
% 21.53/21.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 21.53/21.72  thf('4', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 21.53/21.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 21.53/21.72  thf('5', plain,
% 21.53/21.72      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['3', '4'])).
% 21.53/21.72  thf('6', plain,
% 21.53/21.72      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['2', '5'])).
% 21.53/21.72  thf(t72_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i]:
% 21.53/21.72     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 21.53/21.72  thf('7', plain,
% 21.53/21.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 21.53/21.72         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 21.53/21.72           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 21.53/21.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 21.53/21.72  thf('8', plain,
% 21.53/21.72      (![X0 : $i]: ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['6', '7'])).
% 21.53/21.72  thf(t66_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 21.53/21.72     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 21.53/21.72       ( k2_xboole_0 @
% 21.53/21.72         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 21.53/21.72  thf('9', plain,
% 21.53/21.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 21.53/21.72         X21 : $i]:
% 21.53/21.72         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 21.53/21.72           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 21.53/21.72              (k1_enumset1 @ X19 @ X20 @ X21)))),
% 21.53/21.72      inference('cnf', [status(esa)], [t66_enumset1])).
% 21.53/21.72  thf('10', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 21.53/21.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 21.53/21.72      inference('sup+', [status(thm)], ['8', '9'])).
% 21.53/21.72  thf(t75_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 21.53/21.72     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 21.53/21.72       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 21.53/21.72  thf('11', plain,
% 21.53/21.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 21.53/21.72         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 21.53/21.72           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 21.53/21.72      inference('cnf', [status(esa)], [t75_enumset1])).
% 21.53/21.72  thf(t74_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.53/21.72     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 21.53/21.72       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 21.53/21.72  thf('12', plain,
% 21.53/21.72      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 21.53/21.72         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 21.53/21.72           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 21.53/21.72      inference('cnf', [status(esa)], [t74_enumset1])).
% 21.53/21.72  thf('13', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 21.53/21.72         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 21.53/21.72           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['11', '12'])).
% 21.53/21.72  thf('14', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 21.53/21.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 21.53/21.72      inference('demod', [status(thm)], ['10', '13'])).
% 21.53/21.72  thf(t73_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 21.53/21.72     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 21.53/21.72       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 21.53/21.72  thf('15', plain,
% 21.53/21.72      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 21.53/21.72         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 21.53/21.72           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 21.53/21.72      inference('cnf', [status(esa)], [t73_enumset1])).
% 21.53/21.72  thf('16', plain,
% 21.53/21.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 21.53/21.72         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 21.53/21.72           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 21.53/21.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 21.53/21.72  thf('17', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['15', '16'])).
% 21.53/21.72  thf('18', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['14', '17'])).
% 21.53/21.72  thf('19', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X1 @ X0 @ X2))),
% 21.53/21.72      inference('sup+', [status(thm)], ['1', '18'])).
% 21.53/21.72  thf('20', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['14', '17'])).
% 21.53/21.72  thf('21', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X2 @ X1))),
% 21.53/21.72      inference('sup+', [status(thm)], ['19', '20'])).
% 21.53/21.72  thf('22', plain,
% 21.53/21.72      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 21.53/21.72         (k2_tarski @ sk_D @ sk_E))
% 21.53/21.72         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_B @ sk_C @ sk_E) @ 
% 21.53/21.72             (k3_mcart_1 @ sk_B @ sk_C @ sk_D)))),
% 21.53/21.72      inference('demod', [status(thm)], ['0', '21'])).
% 21.53/21.72  thf(t98_enumset1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 21.53/21.72  thf('23', plain,
% 21.53/21.72      (![X50 : $i, X51 : $i, X52 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X50 @ X52 @ X51) = (k1_enumset1 @ X50 @ X51 @ X52))),
% 21.53/21.72      inference('cnf', [status(esa)], [t98_enumset1])).
% 21.53/21.72  thf('24', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['14', '17'])).
% 21.53/21.72  thf('25', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 21.53/21.72      inference('sup+', [status(thm)], ['23', '24'])).
% 21.53/21.72  thf('26', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 21.53/21.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 21.53/21.72      inference('sup+', [status(thm)], ['14', '17'])).
% 21.53/21.72  thf('27', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.53/21.72         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 21.53/21.72      inference('sup+', [status(thm)], ['25', '26'])).
% 21.53/21.72  thf(d3_mcart_1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 21.53/21.72  thf('28', plain,
% 21.53/21.72      (![X63 : $i, X64 : $i, X65 : $i]:
% 21.53/21.72         ((k3_mcart_1 @ X63 @ X64 @ X65)
% 21.53/21.72           = (k4_tarski @ (k4_tarski @ X63 @ X64) @ X65))),
% 21.53/21.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 21.53/21.72  thf('29', plain,
% 21.53/21.72      (![X63 : $i, X64 : $i, X65 : $i]:
% 21.53/21.72         ((k3_mcart_1 @ X63 @ X64 @ X65)
% 21.53/21.72           = (k4_tarski @ (k4_tarski @ X63 @ X64) @ X65))),
% 21.53/21.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 21.53/21.72  thf(t146_zfmisc_1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i,D:$i]:
% 21.53/21.72     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 21.53/21.72       ( k2_enumset1 @
% 21.53/21.72         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 21.53/21.72         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 21.53/21.72  thf('30', plain,
% 21.53/21.72      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X55 @ X58) @ (k2_tarski @ X56 @ X57))
% 21.53/21.72           = (k2_enumset1 @ (k4_tarski @ X55 @ X56) @ 
% 21.53/21.72              (k4_tarski @ X55 @ X57) @ (k4_tarski @ X58 @ X56) @ 
% 21.53/21.72              (k4_tarski @ X58 @ X57)))),
% 21.53/21.72      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 21.53/21.72  thf('31', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 21.53/21.72           (k2_tarski @ X0 @ X3))
% 21.53/21.72           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 21.53/21.72              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 21.53/21.72              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 21.53/21.72      inference('sup+', [status(thm)], ['29', '30'])).
% 21.53/21.72  thf('32', plain,
% 21.53/21.72      (![X63 : $i, X64 : $i, X65 : $i]:
% 21.53/21.72         ((k3_mcart_1 @ X63 @ X64 @ X65)
% 21.53/21.72           = (k4_tarski @ (k4_tarski @ X63 @ X64) @ X65))),
% 21.53/21.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 21.53/21.72  thf('33', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 21.53/21.72           (k2_tarski @ X0 @ X3))
% 21.53/21.72           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 21.53/21.72              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 21.53/21.72              (k4_tarski @ X4 @ X3)))),
% 21.53/21.72      inference('demod', [status(thm)], ['31', '32'])).
% 21.53/21.72  thf('34', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ 
% 21.53/21.72           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 21.53/21.72           (k2_tarski @ X0 @ X3))
% 21.53/21.72           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 21.53/21.72              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 21.53/21.72              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 21.53/21.72      inference('sup+', [status(thm)], ['28', '33'])).
% 21.53/21.72  thf('35', plain,
% 21.53/21.72      (![X63 : $i, X64 : $i, X65 : $i]:
% 21.53/21.72         ((k3_mcart_1 @ X63 @ X64 @ X65)
% 21.53/21.72           = (k4_tarski @ (k4_tarski @ X63 @ X64) @ X65))),
% 21.53/21.72      inference('cnf', [status(esa)], [d3_mcart_1])).
% 21.53/21.72  thf('36', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ 
% 21.53/21.72           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 21.53/21.72           (k2_tarski @ X0 @ X3))
% 21.53/21.72           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 21.53/21.72              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 21.53/21.72              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 21.53/21.72      inference('demod', [status(thm)], ['34', '35'])).
% 21.53/21.72  thf('37', plain,
% 21.53/21.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.53/21.72         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 21.53/21.72           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 21.53/21.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 21.53/21.72  thf('38', plain,
% 21.53/21.72      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X55 @ X58) @ (k2_tarski @ X56 @ X57))
% 21.53/21.72           = (k2_enumset1 @ (k4_tarski @ X55 @ X56) @ 
% 21.53/21.72              (k4_tarski @ X55 @ X57) @ (k4_tarski @ X58 @ X56) @ 
% 21.53/21.72              (k4_tarski @ X58 @ X57)))),
% 21.53/21.72      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 21.53/21.72  thf('39', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0))
% 21.53/21.72           = (k1_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ 
% 21.53/21.72              (k4_tarski @ X1 @ X0)))),
% 21.53/21.72      inference('sup+', [status(thm)], ['37', '38'])).
% 21.53/21.72  thf('40', plain,
% 21.53/21.72      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 21.53/21.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 21.53/21.72  thf('41', plain,
% 21.53/21.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 21.53/21.72      inference('cnf', [status(esa)], [t100_enumset1])).
% 21.53/21.72  thf('42', plain,
% 21.53/21.72      (![X23 : $i, X24 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 21.53/21.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 21.53/21.72  thf('43', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i]:
% 21.53/21.72         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 21.53/21.72      inference('sup+', [status(thm)], ['41', '42'])).
% 21.53/21.72  thf('44', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 21.53/21.72           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X2 @ X0)))),
% 21.53/21.72      inference('demod', [status(thm)], ['39', '40', '43'])).
% 21.53/21.72  thf('45', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 21.53/21.72           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X2 @ X0)))),
% 21.53/21.72      inference('demod', [status(thm)], ['39', '40', '43'])).
% 21.53/21.72  thf(t36_zfmisc_1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 21.53/21.72         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 21.53/21.72       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 21.53/21.72         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 21.53/21.72  thf('46', plain,
% 21.53/21.72      (![X59 : $i, X60 : $i, X62 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X59 @ X60) @ (k1_tarski @ X62))
% 21.53/21.72           = (k2_tarski @ (k4_tarski @ X59 @ X62) @ (k4_tarski @ X60 @ X62)))),
% 21.53/21.72      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 21.53/21.72  thf('47', plain,
% 21.53/21.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.53/21.72         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X0))
% 21.53/21.72           = (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 21.53/21.72      inference('sup+', [status(thm)], ['45', '46'])).
% 21.53/21.72  thf(d3_zfmisc_1, axiom,
% 21.53/21.72    (![A:$i,B:$i,C:$i]:
% 21.53/21.72     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 21.53/21.72       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 21.53/21.72  thf('48', plain,
% 21.53/21.72      (![X66 : $i, X67 : $i, X68 : $i]:
% 21.53/21.72         ((k3_zfmisc_1 @ X66 @ X67 @ X68)
% 21.53/21.72           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67) @ X68))),
% 21.53/21.72      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 21.53/21.72  thf('49', plain,
% 21.53/21.72      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 21.53/21.72         (k2_tarski @ sk_D @ sk_E))
% 21.53/21.72         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 21.53/21.72             (k2_tarski @ sk_D @ sk_E)))),
% 21.53/21.72      inference('demod', [status(thm)], ['22', '27', '36', '44', '47', '48'])).
% 21.53/21.72  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 21.53/21.72  
% 21.53/21.72  % SZS output end Refutation
% 21.53/21.72  
% 21.53/21.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
