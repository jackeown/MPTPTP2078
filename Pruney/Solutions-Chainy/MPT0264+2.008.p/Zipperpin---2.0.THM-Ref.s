%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HS3dxTDPrO

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:39 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 401 expanded)
%              Number of leaves         :   37 ( 145 expanded)
%              Depth                    :   19
%              Number of atoms          :  839 (2891 expanded)
%              Number of equality atoms :   94 ( 370 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_2 ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_xboole_0 @ ( k2_tarski @ X54 @ X55 ) @ ( k2_tarski @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ X33 @ ( k4_xboole_0 @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ X33 @ ( k4_xboole_0 @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['14','19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X28: $i] :
      ( r1_tarski @ k1_xboole_0 @ X28 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
        = ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ ( k2_xboole_0 @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('42',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X47 @ X46 @ X45 @ X44 )
      = ( k2_enumset1 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_enumset1 @ X69 @ X69 @ X70 )
      = ( k2_tarski @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k1_enumset1 @ X51 @ X52 @ X53 )
      = ( k2_xboole_0 @ ( k1_tarski @ X51 ) @ ( k2_tarski @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('48',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('49',plain,(
    ! [X82: $i,X84: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X82 ) @ X84 )
        = ( k1_tarski @ X82 ) )
      | ( r2_hidden @ X82 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('52',plain,(
    ! [X87: $i,X88: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X87 ) @ X88 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,(
    r2_hidden @ sk_B_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ( r2_hidden @ sk_B_2 @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_2 @ ( k3_xboole_0 @ ( k2_tarski @ sk_B_2 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_2 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('63',plain,(
    r2_hidden @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','62'])).

thf('64',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k1_enumset1 @ X69 @ X69 @ X70 )
      = ( k2_tarski @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('65',plain,(
    ! [X71: $i] :
      ( ( k1_enumset1 @ X71 @ X71 @ X71 )
      = ( k1_tarski @ X71 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t136_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X49 = X48 )
      | ( ( k4_xboole_0 @ ( k1_enumset1 @ X49 @ X48 @ X50 ) @ ( k1_tarski @ X49 ) )
        = ( k2_tarski @ X48 @ X50 ) )
      | ( X49 = X50 ) ) ),
    inference(cnf,[status(esa)],[t136_enumset1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('69',plain,(
    ! [X82: $i,X84: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X82 ) @ X84 )
        = ( k1_tarski @ X82 ) )
      | ( r2_hidden @ X82 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('73',plain,(
    ! [X79: $i,X81: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X79 ) @ X81 )
      | ~ ( r2_hidden @ X79 @ X81 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('75',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r1_xboole_0 @ X37 @ ( k4_xboole_0 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t54_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('77',plain,(
    ! [X89: $i,X90: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X89 ) @ X90 )
      | ~ ( r2_hidden @ X89 @ X90 ) ) ),
    inference(cnf,[status(esa)],[t54_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = X0 )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['66','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    sk_B_2 = sk_A ),
    inference('sup-',[status(thm)],['63','81'])).

thf('83',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HS3dxTDPrO
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.35/3.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.35/3.60  % Solved by: fo/fo7.sh
% 3.35/3.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.60  % done 5496 iterations in 3.146s
% 3.35/3.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.35/3.60  % SZS output start Refutation
% 3.35/3.60  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.35/3.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.35/3.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.35/3.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.35/3.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.35/3.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.35/3.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.35/3.60  thf(sk_C_type, type, sk_C: $i).
% 3.35/3.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.35/3.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.35/3.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.35/3.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.35/3.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.35/3.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.35/3.60  thf(t59_zfmisc_1, conjecture,
% 3.35/3.60    (![A:$i,B:$i,C:$i]:
% 3.35/3.60     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 3.35/3.60          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 3.35/3.60  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.60    (~( ![A:$i,B:$i,C:$i]:
% 3.35/3.60        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 3.35/3.60             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 3.35/3.60    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 3.35/3.60  thf('0', plain,
% 3.35/3.60      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_2) @ sk_C) = (k1_tarski @ sk_A))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf(t45_enumset1, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.60     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.35/3.60       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.35/3.60  thf('1', plain,
% 3.35/3.60      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 3.35/3.60         ((k2_enumset1 @ X54 @ X55 @ X56 @ X57)
% 3.35/3.60           = (k2_xboole_0 @ (k2_tarski @ X54 @ X55) @ (k2_tarski @ X56 @ X57)))),
% 3.35/3.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 3.35/3.60  thf(t22_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.35/3.60  thf('2', plain,
% 3.35/3.60      (![X23 : $i, X24 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)) = (X23))),
% 3.35/3.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.35/3.60  thf(t46_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.35/3.60  thf('3', plain,
% 3.35/3.60      (![X31 : $i, X32 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X31 @ (k2_xboole_0 @ X31 @ X32)) = (k1_xboole_0))),
% 3.35/3.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.35/3.60  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['2', '3'])).
% 3.35/3.60  thf(t48_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.35/3.60  thf('5', plain,
% 3.35/3.60      (![X33 : $i, X34 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X33 @ (k4_xboole_0 @ X33 @ X34))
% 3.35/3.60           = (k3_xboole_0 @ X33 @ X34))),
% 3.35/3.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.35/3.60  thf('6', plain,
% 3.35/3.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['4', '5'])).
% 3.35/3.60  thf('7', plain,
% 3.35/3.60      (![X23 : $i, X24 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)) = (X23))),
% 3.35/3.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.35/3.60  thf(commutativity_k2_xboole_0, axiom,
% 3.35/3.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.35/3.60  thf('8', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.35/3.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.35/3.60  thf('9', plain,
% 3.35/3.60      (![X31 : $i, X32 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X31 @ (k2_xboole_0 @ X31 @ X32)) = (k1_xboole_0))),
% 3.35/3.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.35/3.60  thf('10', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['8', '9'])).
% 3.35/3.60  thf('11', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['7', '10'])).
% 3.35/3.60  thf('12', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['6', '11'])).
% 3.35/3.60  thf(d6_xboole_0, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k5_xboole_0 @ A @ B ) =
% 3.35/3.60       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.35/3.60  thf('13', plain,
% 3.35/3.60      (![X11 : $i, X12 : $i]:
% 3.35/3.60         ((k5_xboole_0 @ X11 @ X12)
% 3.35/3.60           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 3.35/3.60              (k4_xboole_0 @ X12 @ X11)))),
% 3.35/3.60      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.35/3.60  thf('14', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.35/3.60           = (k2_xboole_0 @ 
% 3.35/3.60              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 3.35/3.60              k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['12', '13'])).
% 3.35/3.60  thf('15', plain,
% 3.35/3.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['4', '5'])).
% 3.35/3.60  thf(t100_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.35/3.60  thf('16', plain,
% 3.35/3.60      (![X18 : $i, X19 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X18 @ X19)
% 3.35/3.60           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 3.35/3.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.35/3.60  thf('17', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X0 @ X0)
% 3.35/3.60           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.35/3.60      inference('sup+', [status(thm)], ['15', '16'])).
% 3.35/3.60  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['2', '3'])).
% 3.35/3.60  thf('19', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.35/3.60      inference('demod', [status(thm)], ['17', '18'])).
% 3.35/3.60  thf('20', plain,
% 3.35/3.60      (![X33 : $i, X34 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X33 @ (k4_xboole_0 @ X33 @ X34))
% 3.35/3.60           = (k3_xboole_0 @ X33 @ X34))),
% 3.35/3.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.35/3.60  thf('21', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.35/3.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.35/3.60  thf('22', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k1_xboole_0)
% 3.35/3.60           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.35/3.60      inference('demod', [status(thm)], ['14', '19', '20', '21'])).
% 3.35/3.60  thf('23', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['8', '9'])).
% 3.35/3.60  thf('24', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.35/3.60           = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['22', '23'])).
% 3.35/3.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.35/3.60  thf('25', plain, (![X28 : $i]: (r1_tarski @ k1_xboole_0 @ X28)),
% 3.35/3.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.35/3.60  thf(t45_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( r1_tarski @ A @ B ) =>
% 3.35/3.60       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 3.35/3.60  thf('26', plain,
% 3.35/3.60      (![X29 : $i, X30 : $i]:
% 3.35/3.60         (((X30) = (k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))
% 3.35/3.60          | ~ (r1_tarski @ X29 @ X30))),
% 3.35/3.60      inference('cnf', [status(esa)], [t45_xboole_1])).
% 3.35/3.60  thf('27', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['25', '26'])).
% 3.35/3.60  thf('28', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 3.35/3.60           = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['24', '27'])).
% 3.35/3.60  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['2', '3'])).
% 3.35/3.60  thf('30', plain,
% 3.35/3.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['4', '5'])).
% 3.35/3.60  thf('31', plain,
% 3.35/3.60      (![X23 : $i, X24 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)) = (X23))),
% 3.35/3.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.35/3.60  thf('32', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['30', '31'])).
% 3.35/3.60  thf('33', plain,
% 3.35/3.60      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['29', '32'])).
% 3.35/3.60  thf('34', plain,
% 3.35/3.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.35/3.60      inference('demod', [status(thm)], ['28', '33'])).
% 3.35/3.60  thf('35', plain,
% 3.35/3.60      (![X23 : $i, X24 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)) = (X23))),
% 3.35/3.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.35/3.60  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['34', '35'])).
% 3.35/3.60  thf(t6_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.35/3.60  thf('37', plain,
% 3.35/3.60      (![X35 : $i, X36 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X35 @ (k2_xboole_0 @ X35 @ X36))
% 3.35/3.60           = (k2_xboole_0 @ X35 @ X36))),
% 3.35/3.60      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.35/3.60  thf('38', plain,
% 3.35/3.60      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['36', '37'])).
% 3.35/3.60  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['34', '35'])).
% 3.35/3.60  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.35/3.60      inference('demod', [status(thm)], ['38', '39'])).
% 3.35/3.60  thf('41', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['1', '40'])).
% 3.35/3.60  thf(t125_enumset1, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.60     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 3.35/3.60  thf('42', plain,
% 3.35/3.60      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.35/3.60         ((k2_enumset1 @ X47 @ X46 @ X45 @ X44)
% 3.35/3.60           = (k2_enumset1 @ X44 @ X45 @ X46 @ X47))),
% 3.35/3.60      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.35/3.60  thf('43', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k2_enumset1 @ X0 @ X1 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['41', '42'])).
% 3.35/3.60  thf('44', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['1', '40'])).
% 3.35/3.60  thf('45', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.35/3.60      inference('sup+', [status(thm)], ['43', '44'])).
% 3.35/3.60  thf(t70_enumset1, axiom,
% 3.35/3.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.35/3.60  thf('46', plain,
% 3.35/3.60      (![X69 : $i, X70 : $i]:
% 3.35/3.60         ((k1_enumset1 @ X69 @ X69 @ X70) = (k2_tarski @ X69 @ X70))),
% 3.35/3.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.35/3.60  thf(t42_enumset1, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i]:
% 3.35/3.60     ( ( k1_enumset1 @ A @ B @ C ) =
% 3.35/3.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 3.35/3.60  thf('47', plain,
% 3.35/3.60      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.35/3.60         ((k1_enumset1 @ X51 @ X52 @ X53)
% 3.35/3.60           = (k2_xboole_0 @ (k1_tarski @ X51) @ (k2_tarski @ X52 @ X53)))),
% 3.35/3.60      inference('cnf', [status(esa)], [t42_enumset1])).
% 3.35/3.60  thf('48', plain,
% 3.35/3.60      (![X31 : $i, X32 : $i]:
% 3.35/3.60         ((k4_xboole_0 @ X31 @ (k2_xboole_0 @ X31 @ X32)) = (k1_xboole_0))),
% 3.35/3.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.35/3.60  thf(l33_zfmisc_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 3.35/3.60       ( ~( r2_hidden @ A @ B ) ) ))).
% 3.35/3.60  thf('49', plain,
% 3.35/3.60      (![X82 : $i, X84 : $i]:
% 3.35/3.60         (((k4_xboole_0 @ (k1_tarski @ X82) @ X84) = (k1_tarski @ X82))
% 3.35/3.60          | (r2_hidden @ X82 @ X84))),
% 3.35/3.60      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 3.35/3.60  thf('50', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         (((k1_xboole_0) = (k1_tarski @ X0))
% 3.35/3.60          | (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 3.35/3.60      inference('sup+', [status(thm)], ['48', '49'])).
% 3.35/3.60  thf('51', plain,
% 3.35/3.60      (![X23 : $i, X24 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24)) = (X23))),
% 3.35/3.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.35/3.60  thf(t49_zfmisc_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 3.35/3.60  thf('52', plain,
% 3.35/3.60      (![X87 : $i, X88 : $i]:
% 3.35/3.60         ((k2_xboole_0 @ (k1_tarski @ X87) @ X88) != (k1_xboole_0))),
% 3.35/3.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 3.35/3.60  thf('53', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['51', '52'])).
% 3.35/3.60  thf('54', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['50', '53'])).
% 3.35/3.60  thf('55', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['47', '54'])).
% 3.35/3.60  thf('56', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['46', '55'])).
% 3.35/3.60  thf('57', plain, ((r2_hidden @ sk_B_2 @ sk_C)),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf(d4_xboole_0, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i]:
% 3.35/3.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.35/3.60       ( ![D:$i]:
% 3.35/3.60         ( ( r2_hidden @ D @ C ) <=>
% 3.35/3.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.35/3.60  thf('58', plain,
% 3.35/3.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X5 @ X6)
% 3.35/3.60          | ~ (r2_hidden @ X5 @ X7)
% 3.35/3.60          | (r2_hidden @ X5 @ X8)
% 3.35/3.60          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 3.35/3.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.35/3.60  thf('59', plain,
% 3.35/3.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.35/3.60         ((r2_hidden @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 3.35/3.60          | ~ (r2_hidden @ X5 @ X7)
% 3.35/3.60          | ~ (r2_hidden @ X5 @ X6))),
% 3.35/3.60      inference('simplify', [status(thm)], ['58'])).
% 3.35/3.60  thf('60', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         (~ (r2_hidden @ sk_B_2 @ X0)
% 3.35/3.60          | (r2_hidden @ sk_B_2 @ (k3_xboole_0 @ X0 @ sk_C)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['57', '59'])).
% 3.35/3.60  thf('61', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         (r2_hidden @ sk_B_2 @ (k3_xboole_0 @ (k2_tarski @ sk_B_2 @ X0) @ sk_C))),
% 3.35/3.60      inference('sup-', [status(thm)], ['56', '60'])).
% 3.35/3.60  thf('62', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         (r2_hidden @ sk_B_2 @ (k3_xboole_0 @ (k2_tarski @ X0 @ sk_B_2) @ sk_C))),
% 3.35/3.60      inference('sup+', [status(thm)], ['45', '61'])).
% 3.35/3.60  thf('63', plain, ((r2_hidden @ sk_B_2 @ (k1_tarski @ sk_A))),
% 3.35/3.60      inference('sup+', [status(thm)], ['0', '62'])).
% 3.35/3.60  thf('64', plain,
% 3.35/3.60      (![X69 : $i, X70 : $i]:
% 3.35/3.60         ((k1_enumset1 @ X69 @ X69 @ X70) = (k2_tarski @ X69 @ X70))),
% 3.35/3.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.35/3.60  thf(t76_enumset1, axiom,
% 3.35/3.60    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.35/3.60  thf('65', plain,
% 3.35/3.60      (![X71 : $i]: ((k1_enumset1 @ X71 @ X71 @ X71) = (k1_tarski @ X71))),
% 3.35/3.60      inference('cnf', [status(esa)], [t76_enumset1])).
% 3.35/3.60  thf('66', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['64', '65'])).
% 3.35/3.60  thf(t136_enumset1, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i]:
% 3.35/3.60     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 3.35/3.60          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 3.35/3.60            ( k2_tarski @ B @ C ) ) ) ))).
% 3.35/3.60  thf('67', plain,
% 3.35/3.60      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.35/3.60         (((X49) = (X48))
% 3.35/3.60          | ((k4_xboole_0 @ (k1_enumset1 @ X49 @ X48 @ X50) @ (k1_tarski @ X49))
% 3.35/3.60              = (k2_tarski @ X48 @ X50))
% 3.35/3.60          | ((X49) = (X50)))),
% 3.35/3.60      inference('cnf', [status(esa)], [t136_enumset1])).
% 3.35/3.60  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.35/3.60      inference('sup+', [status(thm)], ['2', '3'])).
% 3.35/3.60  thf('69', plain,
% 3.35/3.60      (![X82 : $i, X84 : $i]:
% 3.35/3.60         (((k4_xboole_0 @ (k1_tarski @ X82) @ X84) = (k1_tarski @ X82))
% 3.35/3.60          | (r2_hidden @ X82 @ X84))),
% 3.35/3.60      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 3.35/3.60  thf('70', plain,
% 3.35/3.60      (![X0 : $i]:
% 3.35/3.60         (((k1_xboole_0) = (k1_tarski @ X0))
% 3.35/3.60          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.35/3.60      inference('sup+', [status(thm)], ['68', '69'])).
% 3.35/3.60  thf('71', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['51', '52'])).
% 3.35/3.60  thf('72', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 3.35/3.60  thf(l1_zfmisc_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 3.35/3.60  thf('73', plain,
% 3.35/3.60      (![X79 : $i, X81 : $i]:
% 3.35/3.60         ((r1_tarski @ (k1_tarski @ X79) @ X81) | ~ (r2_hidden @ X79 @ X81))),
% 3.35/3.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.35/3.60  thf('74', plain,
% 3.35/3.60      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 3.35/3.60      inference('sup-', [status(thm)], ['72', '73'])).
% 3.35/3.60  thf(t85_xboole_1, axiom,
% 3.35/3.60    (![A:$i,B:$i,C:$i]:
% 3.35/3.60     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 3.35/3.60  thf('75', plain,
% 3.35/3.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.35/3.60         (~ (r1_tarski @ X37 @ X38)
% 3.35/3.60          | (r1_xboole_0 @ X37 @ (k4_xboole_0 @ X39 @ X38)))),
% 3.35/3.60      inference('cnf', [status(esa)], [t85_xboole_1])).
% 3.35/3.60  thf('76', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         (r1_xboole_0 @ (k1_tarski @ X0) @ 
% 3.35/3.60          (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['74', '75'])).
% 3.35/3.60  thf(t54_zfmisc_1, axiom,
% 3.35/3.60    (![A:$i,B:$i]:
% 3.35/3.60     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 3.35/3.60  thf('77', plain,
% 3.35/3.60      (![X89 : $i, X90 : $i]:
% 3.35/3.60         (~ (r1_xboole_0 @ (k1_tarski @ X89) @ X90) | ~ (r2_hidden @ X89 @ X90))),
% 3.35/3.60      inference('cnf', [status(esa)], [t54_zfmisc_1])).
% 3.35/3.60  thf('78', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['76', '77'])).
% 3.35/3.60  thf('79', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 3.35/3.60          | ((X2) = (X0))
% 3.35/3.60          | ((X2) = (X1)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['67', '78'])).
% 3.35/3.60  thf('80', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 3.35/3.60      inference('sup-', [status(thm)], ['66', '79'])).
% 3.35/3.60  thf('81', plain,
% 3.35/3.60      (![X0 : $i, X1 : $i]:
% 3.35/3.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 3.35/3.60      inference('simplify', [status(thm)], ['80'])).
% 3.35/3.60  thf('82', plain, (((sk_B_2) = (sk_A))),
% 3.35/3.60      inference('sup-', [status(thm)], ['63', '81'])).
% 3.35/3.60  thf('83', plain, (((sk_A) != (sk_B_2))),
% 3.35/3.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.60  thf('84', plain, ($false),
% 3.35/3.60      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 3.35/3.60  
% 3.35/3.60  % SZS output end Refutation
% 3.35/3.60  
% 3.35/3.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
