%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4mEscbCsWf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:49 EST 2020

% Result     : Theorem 4.11s
% Output     : Refutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  157 (1102 expanded)
%              Number of leaves         :   23 ( 333 expanded)
%              Depth                    :   33
%              Number of atoms          : 1363 (9326 expanded)
%              Number of equality atoms :   90 ( 532 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X21
        = ( k4_xboole_0 @ X21 @ ( k2_tarski @ X20 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X21
        = ( k4_xboole_0 @ X21 @ ( k2_tarski @ X20 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('32',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('39',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('59',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('61',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('63',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X1 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('78',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('86',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('88',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('90',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','90'])).

thf('92',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('94',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('96',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('103',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['92','103'])).

thf('105',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('106',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_mcart_1 @ X30 )
        = X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ ( k1_tarski @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ sk_C ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( ( k2_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ sk_C ) )
        = ( k1_mcart_1 @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','107'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('109',plain,(
    ! [X33: $i,X35: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X33 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('110',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('115',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['111'])).

thf('120',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['118','119'])).

thf('121',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['112','120'])).

thf('122',plain,
    ( ( k1_tarski @ sk_B )
    = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['110','121'])).

thf('123',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_mcart_1 @ X30 )
        = X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ ( k1_tarski @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( ( k2_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ sk_B ) )
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','124'])).

thf('126',plain,(
    ! [X33: $i,X35: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X33 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('127',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['116'])).

thf('129',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['116'])).

thf('130',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['118','129'])).

thf('131',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['128','130'])).

thf('132',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4mEscbCsWf
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 4.11/4.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.11/4.37  % Solved by: fo/fo7.sh
% 4.11/4.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.11/4.37  % done 3747 iterations in 3.922s
% 4.11/4.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.11/4.37  % SZS output start Refutation
% 4.11/4.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.11/4.37  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 4.11/4.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.11/4.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.11/4.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.11/4.37  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.11/4.37  thf(sk_C_type, type, sk_C: $i).
% 4.11/4.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.11/4.37  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 4.11/4.37  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.11/4.37  thf(sk_A_type, type, sk_A: $i).
% 4.11/4.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.11/4.37  thf(sk_B_type, type, sk_B: $i).
% 4.11/4.37  thf(d10_xboole_0, axiom,
% 4.11/4.37    (![A:$i,B:$i]:
% 4.11/4.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.11/4.37  thf('0', plain,
% 4.11/4.37      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 4.11/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.11/4.37  thf('1', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 4.11/4.37      inference('simplify', [status(thm)], ['0'])).
% 4.11/4.37  thf(t38_zfmisc_1, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i]:
% 4.11/4.37     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 4.11/4.37       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 4.11/4.37  thf('2', plain,
% 4.11/4.37      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.11/4.37         ((r2_hidden @ X23 @ X24)
% 4.11/4.37          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 4.11/4.37      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.11/4.37  thf('3', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.11/4.37  thf(t69_enumset1, axiom,
% 4.11/4.37    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.11/4.37  thf('4', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.11/4.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.37  thf('5', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.11/4.37  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf(l54_zfmisc_1, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i,D:$i]:
% 4.11/4.37     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 4.11/4.37       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 4.11/4.37  thf('7', plain,
% 4.11/4.37      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 4.11/4.37         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 4.11/4.37          | ~ (r2_hidden @ X17 @ X19)
% 4.11/4.37          | ~ (r2_hidden @ X15 @ X16))),
% 4.11/4.37      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.11/4.37  thf('8', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X1)
% 4.11/4.37          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 4.11/4.37             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['6', '7'])).
% 4.11/4.37  thf('9', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (r2_hidden @ (k4_tarski @ X1 @ X2) @ 
% 4.11/4.37          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['3', '8'])).
% 4.11/4.37  thf('10', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (r2_hidden @ (k4_tarski @ X1 @ X2) @ 
% 4.11/4.37          (k2_zfmisc_1 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['3', '8'])).
% 4.11/4.37  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf(t15_mcart_1, conjecture,
% 4.11/4.37    (![A:$i,B:$i,C:$i,D:$i]:
% 4.11/4.37     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 4.11/4.37       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 4.11/4.37         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 4.11/4.37  thf(zf_stmt_0, negated_conjecture,
% 4.11/4.37    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.11/4.37        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 4.11/4.37          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 4.11/4.37            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 4.11/4.37    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 4.11/4.37  thf('14', plain,
% 4.11/4.37      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 4.11/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.37  thf(t10_mcart_1, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i]:
% 4.11/4.37     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 4.11/4.37       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 4.11/4.37         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 4.11/4.37  thf('15', plain,
% 4.11/4.37      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.11/4.37         ((r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 4.11/4.37          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 4.11/4.37      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.11/4.37  thf('16', plain,
% 4.11/4.37      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 4.11/4.37      inference('sup-', [status(thm)], ['14', '15'])).
% 4.11/4.37  thf(t144_zfmisc_1, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i]:
% 4.11/4.37     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 4.11/4.37          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 4.11/4.37  thf('17', plain,
% 4.11/4.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.11/4.37         ((r2_hidden @ X20 @ X21)
% 4.11/4.37          | (r2_hidden @ X22 @ X21)
% 4.11/4.37          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 4.11/4.37      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 4.11/4.37  thf(d5_xboole_0, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i]:
% 4.11/4.37     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.11/4.37       ( ![D:$i]:
% 4.11/4.37         ( ( r2_hidden @ D @ C ) <=>
% 4.11/4.37           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.11/4.37  thf('18', plain,
% 4.11/4.37      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X4 @ X3)
% 4.11/4.37          | ~ (r2_hidden @ X4 @ X2)
% 4.11/4.37          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.11/4.37      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.11/4.37  thf('19', plain,
% 4.11/4.37      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X4 @ X2)
% 4.11/4.37          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.11/4.37      inference('simplify', [status(thm)], ['18'])).
% 4.11/4.37  thf('20', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X3 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | (r2_hidden @ X2 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['17', '19'])).
% 4.11/4.37  thf('21', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ sk_B @ X0)
% 4.11/4.37          | (r2_hidden @ sk_C @ X0)
% 4.11/4.37          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['16', '20'])).
% 4.11/4.37  thf('22', plain,
% 4.11/4.37      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['13', '21'])).
% 4.11/4.37  thf('23', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.11/4.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.37  thf('24', plain,
% 4.11/4.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.11/4.37         ((r2_hidden @ X20 @ X21)
% 4.11/4.37          | (r2_hidden @ X22 @ X21)
% 4.11/4.37          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 4.11/4.37      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 4.11/4.37  thf('25', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 4.11/4.37          | (r2_hidden @ X0 @ X1)
% 4.11/4.37          | (r2_hidden @ X0 @ X1))),
% 4.11/4.37      inference('sup+', [status(thm)], ['23', '24'])).
% 4.11/4.37  thf('26', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         ((r2_hidden @ X0 @ X1)
% 4.11/4.37          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 4.11/4.37      inference('simplify', [status(thm)], ['25'])).
% 4.11/4.37  thf('27', plain,
% 4.11/4.37      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X4 @ X2)
% 4.11/4.37          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.11/4.37      inference('simplify', [status(thm)], ['18'])).
% 4.11/4.37  thf('28', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['26', '27'])).
% 4.11/4.37  thf('29', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.11/4.37          | ~ (r2_hidden @ sk_C @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['22', '28'])).
% 4.11/4.37  thf('30', plain,
% 4.11/4.37      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 4.11/4.37        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['12', '29'])).
% 4.11/4.37  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('32', plain,
% 4.11/4.37      (![X23 : $i, X25 : $i, X26 : $i]:
% 4.11/4.37         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 4.11/4.37          | ~ (r2_hidden @ X25 @ X26)
% 4.11/4.37          | ~ (r2_hidden @ X23 @ X26))),
% 4.11/4.37      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.11/4.37  thf('33', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['31', '32'])).
% 4.11/4.37  thf('34', plain,
% 4.11/4.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_C) @ 
% 4.11/4.37           (k1_tarski @ sk_C)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['30', '33'])).
% 4.11/4.37  thf('35', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 4.11/4.37      inference('simplify', [status(thm)], ['0'])).
% 4.11/4.37  thf('36', plain,
% 4.11/4.37      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.11/4.37         ((r2_hidden @ X25 @ X24)
% 4.11/4.37          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 4.11/4.37      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.11/4.37  thf('37', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['35', '36'])).
% 4.11/4.37  thf('38', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.11/4.37  thf('39', plain,
% 4.11/4.37      (![X23 : $i, X25 : $i, X26 : $i]:
% 4.11/4.37         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 4.11/4.37          | ~ (r2_hidden @ X25 @ X26)
% 4.11/4.37          | ~ (r2_hidden @ X23 @ X26))),
% 4.11/4.37      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.11/4.37  thf('40', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['38', '39'])).
% 4.11/4.37  thf('41', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['37', '40'])).
% 4.11/4.37  thf('42', plain,
% 4.11/4.37      (![X6 : $i, X8 : $i]:
% 4.11/4.37         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.11/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.11/4.37  thf('43', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['41', '42'])).
% 4.11/4.37  thf('44', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['37', '40'])).
% 4.11/4.37  thf('45', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('demod', [status(thm)], ['43', '44'])).
% 4.11/4.37  thf('46', plain,
% 4.11/4.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 4.11/4.37           (k1_tarski @ sk_C)))),
% 4.11/4.37      inference('demod', [status(thm)], ['34', '45'])).
% 4.11/4.37  thf('47', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.11/4.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.37  thf('48', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.11/4.37  thf('49', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['38', '39'])).
% 4.11/4.37  thf('50', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['48', '49'])).
% 4.11/4.37  thf('51', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('sup+', [status(thm)], ['47', '50'])).
% 4.11/4.37  thf('52', plain,
% 4.11/4.37      (![X6 : $i, X8 : $i]:
% 4.11/4.37         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.11/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.11/4.37  thf('53', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['51', '52'])).
% 4.11/4.37  thf('54', plain,
% 4.11/4.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['46', '53'])).
% 4.11/4.37  thf('55', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['26', '27'])).
% 4.11/4.37  thf('56', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         (((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.11/4.37          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.11/4.37          | ~ (r2_hidden @ sk_B @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['54', '55'])).
% 4.11/4.37  thf('57', plain,
% 4.11/4.37      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['11', '56'])).
% 4.11/4.37  thf('58', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['31', '32'])).
% 4.11/4.37  thf('59', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 4.11/4.37           (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['57', '58'])).
% 4.11/4.37  thf('60', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('demod', [status(thm)], ['43', '44'])).
% 4.11/4.37  thf('61', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.11/4.37           (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('demod', [status(thm)], ['59', '60'])).
% 4.11/4.37  thf('62', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['51', '52'])).
% 4.11/4.37  thf('63', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.11/4.37        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['61', '62'])).
% 4.11/4.37  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('65', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('66', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['1', '2'])).
% 4.11/4.37  thf('67', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.11/4.37          | ~ (r2_hidden @ sk_C @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['22', '28'])).
% 4.11/4.37  thf('68', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 4.11/4.37          | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['66', '67'])).
% 4.11/4.37  thf('69', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['26', '27'])).
% 4.11/4.37  thf('70', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X1))
% 4.11/4.37          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.11/4.37          | ~ (r2_hidden @ sk_B @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['68', '69'])).
% 4.11/4.37  thf('71', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['65', '70'])).
% 4.11/4.37  thf('72', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.11/4.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.37  thf('73', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['26', '27'])).
% 4.11/4.37  thf('74', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 4.11/4.37          | (r2_hidden @ X0 @ X2)
% 4.11/4.37          | ~ (r2_hidden @ X1 @ X2))),
% 4.11/4.37      inference('sup-', [status(thm)], ['72', '73'])).
% 4.11/4.37  thf('75', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.11/4.37          | (r2_hidden @ sk_C @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['71', '74'])).
% 4.11/4.37  thf('76', plain,
% 4.11/4.37      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['64', '75'])).
% 4.11/4.37  thf('77', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['31', '32'])).
% 4.11/4.37  thf('78', plain,
% 4.11/4.37      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 4.11/4.37           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['76', '77'])).
% 4.11/4.37  thf('79', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('demod', [status(thm)], ['43', '44'])).
% 4.11/4.37  thf('80', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('sup+', [status(thm)], ['47', '50'])).
% 4.11/4.37  thf('81', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['79', '80'])).
% 4.11/4.37  thf('82', plain,
% 4.11/4.37      (![X6 : $i, X8 : $i]:
% 4.11/4.37         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.11/4.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.11/4.37  thf('83', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['81', '82'])).
% 4.11/4.37  thf('84', plain,
% 4.11/4.37      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.11/4.37            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['78', '83'])).
% 4.11/4.37  thf('85', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['31', '32'])).
% 4.11/4.37  thf('86', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.11/4.37          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 4.11/4.37           (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['84', '85'])).
% 4.11/4.37  thf('87', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.11/4.37      inference('demod', [status(thm)], ['43', '44'])).
% 4.11/4.37  thf('88', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.11/4.37          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.11/4.37           (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('demod', [status(thm)], ['86', '87'])).
% 4.11/4.37  thf('89', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['51', '52'])).
% 4.11/4.37  thf('90', plain,
% 4.11/4.37      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.11/4.37          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['88', '89'])).
% 4.11/4.37  thf('91', plain,
% 4.11/4.37      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.11/4.37        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.11/4.37      inference('sup+', [status(thm)], ['63', '90'])).
% 4.11/4.37  thf('92', plain,
% 4.11/4.37      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('simplify', [status(thm)], ['91'])).
% 4.11/4.37  thf('93', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.37      inference('sup+', [status(thm)], ['4', '5'])).
% 4.11/4.37  thf('94', plain,
% 4.11/4.37      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('simplify', [status(thm)], ['91'])).
% 4.11/4.37  thf('95', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['35', '36'])).
% 4.11/4.37  thf('96', plain,
% 4.11/4.37      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup+', [status(thm)], ['94', '95'])).
% 4.11/4.37  thf('97', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X2 @ X0)
% 4.11/4.37          | (r2_hidden @ X1 @ X0)
% 4.11/4.37          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['26', '27'])).
% 4.11/4.37  thf('98', plain,
% 4.11/4.37      (![X0 : $i]:
% 4.11/4.37         (((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37          | (r2_hidden @ sk_B @ X0)
% 4.11/4.37          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.11/4.37      inference('sup-', [status(thm)], ['96', '97'])).
% 4.11/4.37  thf('99', plain,
% 4.11/4.37      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['93', '98'])).
% 4.11/4.37  thf('100', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.37          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['31', '32'])).
% 4.11/4.37  thf('101', plain,
% 4.11/4.37      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.11/4.37           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['99', '100'])).
% 4.11/4.37  thf('102', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 4.11/4.37          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['81', '82'])).
% 4.11/4.37  thf('103', plain,
% 4.11/4.37      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A))
% 4.11/4.37            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['101', '102'])).
% 4.11/4.37  thf('104', plain,
% 4.11/4.37      ((((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup+', [status(thm)], ['92', '103'])).
% 4.11/4.37  thf('105', plain,
% 4.11/4.37      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('simplify', [status(thm)], ['104'])).
% 4.11/4.37  thf(t13_mcart_1, axiom,
% 4.11/4.37    (![A:$i,B:$i,C:$i]:
% 4.11/4.37     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 4.11/4.37       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 4.11/4.37         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 4.11/4.37  thf('106', plain,
% 4.11/4.37      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.11/4.37         (((k2_mcart_1 @ X30) = (X32))
% 4.11/4.37          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ (k1_tarski @ X32))))),
% 4.11/4.37      inference('cnf', [status(esa)], [t13_mcart_1])).
% 4.11/4.37  thf('107', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X0 @ (k1_tarski @ sk_C)))
% 4.11/4.37          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.11/4.37          | ((k2_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['105', '106'])).
% 4.11/4.37  thf('108', plain,
% 4.11/4.37      (![X1 : $i]:
% 4.11/4.37         (((k2_mcart_1 @ (k4_tarski @ X1 @ sk_C)) = (k1_mcart_1 @ sk_A))
% 4.11/4.37          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('sup-', [status(thm)], ['10', '107'])).
% 4.11/4.37  thf(t7_mcart_1, axiom,
% 4.11/4.37    (![A:$i,B:$i]:
% 4.11/4.37     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 4.11/4.37       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 4.11/4.37  thf('109', plain,
% 4.11/4.37      (![X33 : $i, X35 : $i]: ((k2_mcart_1 @ (k4_tarski @ X33 @ X35)) = (X35))),
% 4.11/4.37      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.11/4.37  thf('110', plain,
% 4.11/4.37      ((((sk_C) = (k1_mcart_1 @ sk_A))
% 4.11/4.37        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.11/4.37      inference('demod', [status(thm)], ['108', '109'])).
% 4.11/4.37  thf('111', plain,
% 4.11/4.37      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 4.11/4.37        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.11/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.37  thf('112', plain,
% 4.11/4.37      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 4.11/4.37         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 4.11/4.37      inference('split', [status(esa)], ['111'])).
% 4.11/4.37  thf('113', plain,
% 4.11/4.37      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 4.11/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.37  thf('114', plain,
% 4.11/4.37      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.11/4.37         ((r2_hidden @ (k2_mcart_1 @ X27) @ X29)
% 4.11/4.37          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 4.11/4.37      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.11/4.37  thf('115', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 4.11/4.37      inference('sup-', [status(thm)], ['113', '114'])).
% 4.11/4.37  thf('116', plain,
% 4.11/4.37      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 4.11/4.37        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.11/4.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.37  thf('117', plain,
% 4.11/4.37      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))
% 4.11/4.37         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)))),
% 4.11/4.37      inference('split', [status(esa)], ['116'])).
% 4.11/4.37  thf('118', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.11/4.37      inference('sup-', [status(thm)], ['115', '117'])).
% 4.11/4.37  thf('119', plain,
% 4.11/4.37      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 4.11/4.37       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.11/4.37      inference('split', [status(esa)], ['111'])).
% 4.11/4.37  thf('120', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 4.11/4.37      inference('sat_resolution*', [status(thm)], ['118', '119'])).
% 4.11/4.37  thf('121', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 4.11/4.37      inference('simpl_trail', [status(thm)], ['112', '120'])).
% 4.11/4.37  thf('122', plain, (((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 4.11/4.37      inference('simplify_reflect-', [status(thm)], ['110', '121'])).
% 4.11/4.37  thf('123', plain,
% 4.11/4.37      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.11/4.37         (((k2_mcart_1 @ X30) = (X32))
% 4.11/4.37          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ (k1_tarski @ X32))))),
% 4.11/4.37      inference('cnf', [status(esa)], [t13_mcart_1])).
% 4.11/4.37  thf('124', plain,
% 4.11/4.37      (![X0 : $i, X1 : $i]:
% 4.11/4.37         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X0 @ (k1_tarski @ sk_B)))
% 4.11/4.37          | ((k2_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 4.11/4.37      inference('sup-', [status(thm)], ['122', '123'])).
% 4.11/4.37  thf('125', plain,
% 4.11/4.37      (![X1 : $i]:
% 4.11/4.37         ((k2_mcart_1 @ (k4_tarski @ X1 @ sk_B)) = (k1_mcart_1 @ sk_A))),
% 4.11/4.37      inference('sup-', [status(thm)], ['9', '124'])).
% 4.11/4.37  thf('126', plain,
% 4.11/4.37      (![X33 : $i, X35 : $i]: ((k2_mcart_1 @ (k4_tarski @ X33 @ X35)) = (X35))),
% 4.11/4.37      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.11/4.37  thf('127', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 4.11/4.37      inference('demod', [status(thm)], ['125', '126'])).
% 4.11/4.37  thf('128', plain,
% 4.11/4.37      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 4.11/4.37         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 4.11/4.37      inference('split', [status(esa)], ['116'])).
% 4.11/4.37  thf('129', plain,
% 4.11/4.37      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 4.11/4.37       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.11/4.37      inference('split', [status(esa)], ['116'])).
% 4.11/4.37  thf('130', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 4.11/4.37      inference('sat_resolution*', [status(thm)], ['118', '129'])).
% 4.11/4.37  thf('131', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 4.11/4.37      inference('simpl_trail', [status(thm)], ['128', '130'])).
% 4.11/4.37  thf('132', plain, ($false),
% 4.11/4.37      inference('simplify_reflect-', [status(thm)], ['127', '131'])).
% 4.11/4.37  
% 4.11/4.37  % SZS output end Refutation
% 4.11/4.37  
% 4.11/4.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
