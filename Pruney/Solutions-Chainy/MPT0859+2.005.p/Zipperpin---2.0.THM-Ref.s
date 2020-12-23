%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eScqjZZ8ig

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:48 EST 2020

% Result     : Theorem 4.42s
% Output     : Refutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  189 (1356 expanded)
%              Number of leaves         :   24 ( 405 expanded)
%              Depth                    :   31
%              Number of atoms          : 1720 (12440 expanded)
%              Number of equality atoms :  121 ( 778 expanded)
%              Maximal formula depth    :   13 (   7 average)

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

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

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X27 )
        = ( k2_tarski @ X24 @ X26 ) )
      | ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X27 )
        = ( k2_tarski @ X24 @ X26 ) )
      | ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('28',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X22 @ X21 )
      | ~ ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('35',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_C ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('55',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('59',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X1 ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('74',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('82',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('84',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('86',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','86'])).

thf('88',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('90',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('92',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('97',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('103',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('108',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X1 ) @ ( k2_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('112',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_mcart_1 @ X32 )
        = X31 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ ( k1_tarski @ X31 ) @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ ( k2_mcart_1 @ sk_A ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('114',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X34 @ X35 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('117',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['117'])).

thf('119',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('120',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['117'])).

thf('123',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('132',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('133',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('134',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X25 )
       != ( k2_tarski @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
       != ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
     != ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ sk_C ) @ X0 @ X0 )
        = ( k1_mcart_1 @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['101','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','140'])).

thf('144',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('148',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['148'])).

thf('150',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['147','149'])).

thf('151',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['145'])).

thf('152',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['150','151'])).

thf('153',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['146','152'])).

thf('154',plain,
    ( ( k1_tarski @ sk_B )
    = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['144','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','140'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ X0 )
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','140'])).

thf('158',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['148'])).

thf('160',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['148'])).

thf('161',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['150','160'])).

thf('162',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['159','161'])).

thf('163',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eScqjZZ8ig
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.42/4.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.42/4.67  % Solved by: fo/fo7.sh
% 4.42/4.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.42/4.67  % done 3809 iterations in 4.212s
% 4.42/4.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.42/4.67  % SZS output start Refutation
% 4.42/4.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.42/4.67  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 4.42/4.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.42/4.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.42/4.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.42/4.67  thf(sk_C_type, type, sk_C: $i).
% 4.42/4.67  thf(sk_B_type, type, sk_B: $i).
% 4.42/4.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.42/4.67  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 4.42/4.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.42/4.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.42/4.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.42/4.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.42/4.67  thf(sk_A_type, type, sk_A: $i).
% 4.42/4.67  thf(t69_enumset1, axiom,
% 4.42/4.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.42/4.67  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf(d10_xboole_0, axiom,
% 4.42/4.67    (![A:$i,B:$i]:
% 4.42/4.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.42/4.67  thf('1', plain,
% 4.42/4.67      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 4.42/4.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.42/4.67  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 4.42/4.67      inference('simplify', [status(thm)], ['1'])).
% 4.42/4.67  thf(t38_zfmisc_1, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i]:
% 4.42/4.67     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 4.42/4.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 4.42/4.67  thf('3', plain,
% 4.42/4.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.42/4.67         ((r2_hidden @ X20 @ X21)
% 4.42/4.67          | ~ (r1_tarski @ (k2_tarski @ X20 @ X22) @ X21))),
% 4.42/4.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.42/4.67  thf('4', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['2', '3'])).
% 4.42/4.67  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf(t15_mcart_1, conjecture,
% 4.42/4.67    (![A:$i,B:$i,C:$i,D:$i]:
% 4.42/4.67     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 4.42/4.67       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 4.42/4.67         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 4.42/4.67  thf(zf_stmt_0, negated_conjecture,
% 4.42/4.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.42/4.67        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 4.42/4.67          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 4.42/4.67            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 4.42/4.67    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 4.42/4.67  thf('8', plain,
% 4.42/4.67      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 4.42/4.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.67  thf(t10_mcart_1, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i]:
% 4.42/4.67     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 4.42/4.67       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 4.42/4.67         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 4.42/4.67  thf('9', plain,
% 4.42/4.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.42/4.67         ((r2_hidden @ (k1_mcart_1 @ X28) @ X29)
% 4.42/4.67          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 4.42/4.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.42/4.67  thf('10', plain,
% 4.42/4.67      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 4.42/4.67      inference('sup-', [status(thm)], ['8', '9'])).
% 4.42/4.67  thf(t72_zfmisc_1, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i]:
% 4.42/4.67     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 4.42/4.67       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 4.42/4.67  thf('11', plain,
% 4.42/4.67      (![X24 : $i, X26 : $i, X27 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X27)
% 4.42/4.67            = (k2_tarski @ X24 @ X26))
% 4.42/4.67          | (r2_hidden @ X26 @ X27)
% 4.42/4.67          | (r2_hidden @ X24 @ X27))),
% 4.42/4.67      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 4.42/4.67  thf(d5_xboole_0, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i]:
% 4.42/4.67     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.42/4.67       ( ![D:$i]:
% 4.42/4.67         ( ( r2_hidden @ D @ C ) <=>
% 4.42/4.67           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.42/4.67  thf('12', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X3)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.42/4.67  thf('13', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['12'])).
% 4.42/4.67  thf('14', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 4.42/4.67          | (r2_hidden @ X1 @ X2)
% 4.42/4.67          | (r2_hidden @ X0 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X3 @ X2))),
% 4.42/4.67      inference('sup-', [status(thm)], ['11', '13'])).
% 4.42/4.67  thf('15', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         (~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.42/4.67          | (r2_hidden @ sk_C @ X0)
% 4.42/4.67          | (r2_hidden @ sk_B @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['10', '14'])).
% 4.42/4.67  thf('16', plain,
% 4.42/4.67      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['7', '15'])).
% 4.42/4.67  thf('17', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf('18', plain,
% 4.42/4.67      (![X24 : $i, X26 : $i, X27 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X27)
% 4.42/4.67            = (k2_tarski @ X24 @ X26))
% 4.42/4.67          | (r2_hidden @ X26 @ X27)
% 4.42/4.67          | (r2_hidden @ X24 @ X27))),
% 4.42/4.67      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 4.42/4.67  thf('19', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | (r2_hidden @ X0 @ X1))),
% 4.42/4.67      inference('sup+', [status(thm)], ['17', '18'])).
% 4.42/4.67  thf('20', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ X0 @ X1)
% 4.42/4.67          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['19'])).
% 4.42/4.67  thf('21', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf('22', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 4.42/4.67          | (r2_hidden @ X1 @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['20', '21'])).
% 4.42/4.67  thf('23', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['12'])).
% 4.42/4.67  thf('24', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['22', '23'])).
% 4.42/4.67  thf('25', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67          | ~ (r2_hidden @ sk_C @ X0)
% 4.42/4.67          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['16', '24'])).
% 4.42/4.67  thf('26', plain,
% 4.42/4.67      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 4.42/4.67        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['6', '25'])).
% 4.42/4.67  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('28', plain,
% 4.42/4.67      (![X20 : $i, X22 : $i, X23 : $i]:
% 4.42/4.67         ((r1_tarski @ (k2_tarski @ X20 @ X22) @ X23)
% 4.42/4.67          | ~ (r2_hidden @ X22 @ X23)
% 4.42/4.67          | ~ (r2_hidden @ X20 @ X23))),
% 4.42/4.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.42/4.67  thf('29', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['27', '28'])).
% 4.42/4.67  thf('30', plain,
% 4.42/4.67      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_C) @ 
% 4.42/4.67           (k1_tarski @ sk_C)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['26', '29'])).
% 4.42/4.67  thf('31', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 4.42/4.67      inference('simplify', [status(thm)], ['1'])).
% 4.42/4.67  thf('32', plain,
% 4.42/4.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.42/4.67         ((r2_hidden @ X22 @ X21)
% 4.42/4.67          | ~ (r1_tarski @ (k2_tarski @ X20 @ X22) @ X21))),
% 4.42/4.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.42/4.67  thf('33', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['31', '32'])).
% 4.42/4.67  thf('34', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['2', '3'])).
% 4.42/4.67  thf('35', plain,
% 4.42/4.67      (![X20 : $i, X22 : $i, X23 : $i]:
% 4.42/4.67         ((r1_tarski @ (k2_tarski @ X20 @ X22) @ X23)
% 4.42/4.67          | ~ (r2_hidden @ X22 @ X23)
% 4.42/4.67          | ~ (r2_hidden @ X20 @ X23))),
% 4.42/4.67      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 4.42/4.67  thf('36', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['34', '35'])).
% 4.42/4.67  thf('37', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['33', '36'])).
% 4.42/4.67  thf('38', plain,
% 4.42/4.67      (![X6 : $i, X8 : $i]:
% 4.42/4.67         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.42/4.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.42/4.67  thf('39', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['37', '38'])).
% 4.42/4.67  thf('40', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['33', '36'])).
% 4.42/4.67  thf('41', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('demod', [status(thm)], ['39', '40'])).
% 4.42/4.67  thf('42', plain,
% 4.42/4.67      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 4.42/4.67           (k1_tarski @ sk_C)))),
% 4.42/4.67      inference('demod', [status(thm)], ['30', '41'])).
% 4.42/4.67  thf('43', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf('44', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['2', '3'])).
% 4.42/4.67  thf('45', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['34', '35'])).
% 4.42/4.67  thf('46', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['44', '45'])).
% 4.42/4.67  thf('47', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('sup+', [status(thm)], ['43', '46'])).
% 4.42/4.67  thf('48', plain,
% 4.42/4.67      (![X6 : $i, X8 : $i]:
% 4.42/4.67         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.42/4.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.42/4.67  thf('49', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['47', '48'])).
% 4.42/4.67  thf('50', plain,
% 4.42/4.67      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['42', '49'])).
% 4.42/4.67  thf('51', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['22', '23'])).
% 4.42/4.67  thf('52', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         (((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.42/4.67          | ~ (r2_hidden @ sk_B @ X0)
% 4.42/4.67          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['50', '51'])).
% 4.42/4.67  thf('53', plain,
% 4.42/4.67      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['5', '52'])).
% 4.42/4.67  thf('54', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['27', '28'])).
% 4.42/4.67  thf('55', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 4.42/4.67           (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['53', '54'])).
% 4.42/4.67  thf('56', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('demod', [status(thm)], ['39', '40'])).
% 4.42/4.67  thf('57', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.42/4.67           (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('demod', [status(thm)], ['55', '56'])).
% 4.42/4.67  thf('58', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['47', '48'])).
% 4.42/4.67  thf('59', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 4.42/4.67        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['57', '58'])).
% 4.42/4.67  thf('60', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('61', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('62', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['2', '3'])).
% 4.42/4.67  thf('63', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67          | ~ (r2_hidden @ sk_C @ X0)
% 4.42/4.67          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['16', '24'])).
% 4.42/4.67  thf('64', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X0))
% 4.42/4.67          | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['62', '63'])).
% 4.42/4.67  thf('65', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['22', '23'])).
% 4.42/4.67  thf('66', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X1))
% 4.42/4.67          | ~ (r2_hidden @ sk_B @ X0)
% 4.42/4.67          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['64', '65'])).
% 4.42/4.67  thf('67', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_C @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['61', '66'])).
% 4.42/4.67  thf('68', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ X0 @ X1)
% 4.42/4.67          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['19'])).
% 4.42/4.67  thf('69', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['12'])).
% 4.42/4.67  thf('70', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k2_tarski @ X0 @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['68', '69'])).
% 4.42/4.67  thf('71', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.42/4.67          | (r2_hidden @ sk_C @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['67', '70'])).
% 4.42/4.67  thf('72', plain,
% 4.42/4.67      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['60', '71'])).
% 4.42/4.67  thf('73', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['27', '28'])).
% 4.42/4.67  thf('74', plain,
% 4.42/4.67      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 4.42/4.67           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['72', '73'])).
% 4.42/4.67  thf('75', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('demod', [status(thm)], ['39', '40'])).
% 4.42/4.67  thf('76', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('sup+', [status(thm)], ['43', '46'])).
% 4.42/4.67  thf('77', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['75', '76'])).
% 4.42/4.67  thf('78', plain,
% 4.42/4.67      (![X6 : $i, X8 : $i]:
% 4.42/4.67         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 4.42/4.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.42/4.67  thf('79', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['77', '78'])).
% 4.42/4.67  thf('80', plain,
% 4.42/4.67      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.42/4.67            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['74', '79'])).
% 4.42/4.67  thf('81', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['27', '28'])).
% 4.42/4.67  thf('82', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.42/4.67          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 4.42/4.67           (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['80', '81'])).
% 4.42/4.67  thf('83', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.42/4.67      inference('demod', [status(thm)], ['39', '40'])).
% 4.42/4.67  thf('84', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.42/4.67          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.42/4.67           (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('demod', [status(thm)], ['82', '83'])).
% 4.42/4.67  thf('85', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['47', '48'])).
% 4.42/4.67  thf('86', plain,
% 4.42/4.67      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 4.42/4.67          = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['84', '85'])).
% 4.42/4.67  thf('87', plain,
% 4.42/4.67      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.42/4.67        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 4.42/4.67      inference('sup+', [status(thm)], ['59', '86'])).
% 4.42/4.67  thf('88', plain,
% 4.42/4.67      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('simplify', [status(thm)], ['87'])).
% 4.42/4.67  thf('89', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.42/4.67      inference('sup+', [status(thm)], ['0', '4'])).
% 4.42/4.67  thf('90', plain,
% 4.42/4.67      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('simplify', [status(thm)], ['87'])).
% 4.42/4.67  thf('91', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['31', '32'])).
% 4.42/4.67  thf('92', plain,
% 4.42/4.67      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup+', [status(thm)], ['90', '91'])).
% 4.42/4.67  thf('93', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.42/4.67          | (r2_hidden @ X0 @ X1)
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['22', '23'])).
% 4.42/4.67  thf('94', plain,
% 4.42/4.67      (![X0 : $i]:
% 4.42/4.67         (((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 4.42/4.67          | (r2_hidden @ sk_B @ X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['92', '93'])).
% 4.42/4.67  thf('95', plain,
% 4.42/4.67      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['89', '94'])).
% 4.42/4.67  thf('96', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.42/4.67          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['27', '28'])).
% 4.42/4.67  thf('97', plain,
% 4.42/4.67      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 4.42/4.67           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['95', '96'])).
% 4.42/4.67  thf('98', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 4.42/4.67          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['77', '78'])).
% 4.42/4.67  thf('99', plain,
% 4.42/4.67      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A))
% 4.42/4.67            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup-', [status(thm)], ['97', '98'])).
% 4.42/4.67  thf('100', plain,
% 4.42/4.67      ((((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('sup+', [status(thm)], ['88', '99'])).
% 4.42/4.67  thf('101', plain,
% 4.42/4.67      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 4.42/4.67        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.67      inference('simplify', [status(thm)], ['100'])).
% 4.42/4.67  thf('102', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.42/4.67         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.42/4.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.42/4.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.42/4.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.42/4.67  thf('103', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.42/4.67         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.42/4.67          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.42/4.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.42/4.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.42/4.67  thf('104', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 4.42/4.67          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 4.42/4.67          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 4.42/4.67          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['102', '103'])).
% 4.42/4.67  thf('105', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 4.42/4.67          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 4.42/4.67      inference('simplify', [status(thm)], ['104'])).
% 4.42/4.67  thf('106', plain,
% 4.42/4.67      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ sk_D_1))),
% 4.42/4.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.67  thf('107', plain,
% 4.42/4.67      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.42/4.67         ((r2_hidden @ (k2_mcart_1 @ X28) @ X30)
% 4.42/4.67          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 4.42/4.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 4.42/4.67  thf('108', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 4.42/4.67      inference('sup-', [status(thm)], ['106', '107'])).
% 4.42/4.67  thf(l54_zfmisc_1, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i,D:$i]:
% 4.42/4.67     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 4.42/4.67       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 4.42/4.67  thf('109', plain,
% 4.42/4.67      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 4.42/4.67         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 4.42/4.67          | ~ (r2_hidden @ X17 @ X19)
% 4.42/4.67          | ~ (r2_hidden @ X15 @ X16))),
% 4.42/4.67      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 4.42/4.67  thf('110', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X1 @ X0)
% 4.42/4.67          | (r2_hidden @ (k4_tarski @ X1 @ (k2_mcart_1 @ sk_A)) @ 
% 4.42/4.67             (k2_zfmisc_1 @ X0 @ sk_D_1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['108', '109'])).
% 4.42/4.67  thf('111', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((X0) = (k4_xboole_0 @ X1 @ X1))
% 4.42/4.67          | (r2_hidden @ 
% 4.42/4.67             (k4_tarski @ (sk_D @ X0 @ X1 @ X1) @ (k2_mcart_1 @ sk_A)) @ 
% 4.42/4.67             (k2_zfmisc_1 @ X0 @ sk_D_1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['105', '110'])).
% 4.42/4.67  thf(t12_mcart_1, axiom,
% 4.42/4.67    (![A:$i,B:$i,C:$i]:
% 4.42/4.67     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 4.42/4.67       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 4.42/4.67         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 4.42/4.67  thf('112', plain,
% 4.42/4.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.42/4.67         (((k1_mcart_1 @ X32) = (X31))
% 4.42/4.67          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ (k1_tarski @ X31) @ X33)))),
% 4.42/4.67      inference('cnf', [status(esa)], [t12_mcart_1])).
% 4.42/4.67  thf('113', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 4.42/4.67          | ((k1_mcart_1 @ 
% 4.42/4.67              (k4_tarski @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ 
% 4.42/4.67               (k2_mcart_1 @ sk_A)))
% 4.42/4.67              = (X0)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['111', '112'])).
% 4.42/4.67  thf(t7_mcart_1, axiom,
% 4.42/4.67    (![A:$i,B:$i]:
% 4.42/4.67     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 4.42/4.67       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 4.42/4.67  thf('114', plain,
% 4.42/4.67      (![X34 : $i, X35 : $i]: ((k1_mcart_1 @ (k4_tarski @ X34 @ X35)) = (X34))),
% 4.42/4.67      inference('cnf', [status(esa)], [t7_mcart_1])).
% 4.42/4.67  thf('115', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 4.42/4.67          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 4.42/4.67      inference('demod', [status(thm)], ['113', '114'])).
% 4.42/4.67  thf('116', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 4.42/4.67          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 4.42/4.67      inference('simplify', [status(thm)], ['104'])).
% 4.42/4.67  thf('117', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.42/4.67         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 4.42/4.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.42/4.67          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.42/4.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.42/4.67  thf('118', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.42/4.67          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.42/4.67      inference('eq_fact', [status(thm)], ['117'])).
% 4.42/4.67  thf('119', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X3)
% 4.42/4.67          | (r2_hidden @ X4 @ X1)
% 4.42/4.67          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.42/4.67  thf('120', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['119'])).
% 4.42/4.67  thf('121', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ X1 @ X0)
% 4.42/4.67            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 4.42/4.67          | (r2_hidden @ 
% 4.42/4.67             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.42/4.67             X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['118', '120'])).
% 4.42/4.67  thf('122', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.42/4.67          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.42/4.67      inference('eq_fact', [status(thm)], ['117'])).
% 4.42/4.67  thf('123', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['12'])).
% 4.42/4.67  thf('124', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ X1 @ X0)
% 4.42/4.67            = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 4.42/4.67          | ~ (r2_hidden @ 
% 4.42/4.67               (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.42/4.67               X0))),
% 4.42/4.67      inference('sup-', [status(thm)], ['122', '123'])).
% 4.42/4.67  thf('125', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         (((k4_xboole_0 @ X0 @ X0)
% 4.42/4.67            = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 4.42/4.67          | ((k4_xboole_0 @ X0 @ X0)
% 4.42/4.67              = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)))),
% 4.42/4.67      inference('sup-', [status(thm)], ['121', '124'])).
% 4.42/4.67  thf('126', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]:
% 4.42/4.67         ((k4_xboole_0 @ X0 @ X0)
% 4.42/4.67           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.42/4.67      inference('simplify', [status(thm)], ['125'])).
% 4.42/4.67  thf('127', plain,
% 4.42/4.67      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X4 @ X2)
% 4.42/4.67          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 4.42/4.67      inference('simplify', [status(thm)], ['12'])).
% 4.42/4.67  thf('128', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.67         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 4.42/4.67          | ~ (r2_hidden @ X2 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['126', '127'])).
% 4.42/4.67  thf('129', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 4.42/4.67      inference('condensation', [status(thm)], ['128'])).
% 4.42/4.67  thf('130', plain,
% 4.42/4.67      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 4.42/4.67      inference('sup-', [status(thm)], ['116', '129'])).
% 4.42/4.67  thf('131', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf('132', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.67  thf('133', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 4.42/4.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.42/4.68  thf('134', plain,
% 4.42/4.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.42/4.68         (~ (r2_hidden @ X24 @ X25)
% 4.42/4.68          | ((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X25)
% 4.42/4.68              != (k2_tarski @ X24 @ X26)))),
% 4.42/4.68      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 4.42/4.68  thf('135', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]:
% 4.42/4.68         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 4.42/4.68          | ~ (r2_hidden @ X0 @ X1))),
% 4.42/4.68      inference('sup-', [status(thm)], ['133', '134'])).
% 4.42/4.68  thf('136', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]:
% 4.42/4.68         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 4.42/4.68          | ~ (r2_hidden @ X0 @ X1))),
% 4.42/4.68      inference('sup-', [status(thm)], ['132', '135'])).
% 4.42/4.68  thf('137', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]:
% 4.42/4.68         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) != (k1_tarski @ X0))
% 4.42/4.68          | ~ (r2_hidden @ X0 @ X1))),
% 4.42/4.68      inference('sup-', [status(thm)], ['131', '136'])).
% 4.42/4.68  thf('138', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]:
% 4.42/4.68         (((k4_xboole_0 @ X0 @ X0) != (k1_tarski @ X1))
% 4.42/4.68          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X1)))),
% 4.42/4.68      inference('sup-', [status(thm)], ['130', '137'])).
% 4.42/4.68  thf('139', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 4.42/4.68      inference('sup-', [status(thm)], ['31', '32'])).
% 4.42/4.68  thf('140', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) != (k1_tarski @ X1))),
% 4.42/4.68      inference('demod', [status(thm)], ['138', '139'])).
% 4.42/4.68  thf('141', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))),
% 4.42/4.68      inference('clc', [status(thm)], ['115', '140'])).
% 4.42/4.68  thf('142', plain,
% 4.42/4.68      (![X0 : $i]:
% 4.42/4.68         (((sk_D @ (k1_tarski @ sk_C) @ X0 @ X0) = (k1_mcart_1 @ sk_A))
% 4.42/4.68          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.68      inference('sup+', [status(thm)], ['101', '141'])).
% 4.42/4.68  thf('143', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))),
% 4.42/4.68      inference('clc', [status(thm)], ['115', '140'])).
% 4.42/4.68  thf('144', plain,
% 4.42/4.68      ((((sk_C) = (k1_mcart_1 @ sk_A))
% 4.42/4.68        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 4.42/4.68      inference('demod', [status(thm)], ['142', '143'])).
% 4.42/4.68  thf('145', plain,
% 4.42/4.68      ((((k1_mcart_1 @ sk_A) != (sk_C))
% 4.42/4.68        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.42/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.68  thf('146', plain,
% 4.42/4.68      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 4.42/4.68         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 4.42/4.68      inference('split', [status(esa)], ['145'])).
% 4.42/4.68  thf('147', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)),
% 4.42/4.68      inference('sup-', [status(thm)], ['106', '107'])).
% 4.42/4.68  thf('148', plain,
% 4.42/4.68      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 4.42/4.68        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.42/4.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.68  thf('149', plain,
% 4.42/4.68      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))
% 4.42/4.68         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1)))),
% 4.42/4.68      inference('split', [status(esa)], ['148'])).
% 4.42/4.68  thf('150', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.42/4.68      inference('sup-', [status(thm)], ['147', '149'])).
% 4.42/4.68  thf('151', plain,
% 4.42/4.68      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 4.42/4.68       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.42/4.68      inference('split', [status(esa)], ['145'])).
% 4.42/4.68  thf('152', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 4.42/4.68      inference('sat_resolution*', [status(thm)], ['150', '151'])).
% 4.42/4.68  thf('153', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 4.42/4.68      inference('simpl_trail', [status(thm)], ['146', '152'])).
% 4.42/4.68  thf('154', plain, (((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 4.42/4.68      inference('simplify_reflect-', [status(thm)], ['144', '153'])).
% 4.42/4.68  thf('155', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))),
% 4.42/4.68      inference('clc', [status(thm)], ['115', '140'])).
% 4.42/4.68  thf('156', plain,
% 4.42/4.68      (![X0 : $i]:
% 4.42/4.68         ((sk_D @ (k1_tarski @ sk_B) @ X0 @ X0) = (k1_mcart_1 @ sk_A))),
% 4.42/4.68      inference('sup+', [status(thm)], ['154', '155'])).
% 4.42/4.68  thf('157', plain,
% 4.42/4.68      (![X0 : $i, X1 : $i]: ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))),
% 4.42/4.68      inference('clc', [status(thm)], ['115', '140'])).
% 4.42/4.68  thf('158', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 4.42/4.68      inference('demod', [status(thm)], ['156', '157'])).
% 4.42/4.68  thf('159', plain,
% 4.42/4.68      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 4.42/4.68         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 4.42/4.68      inference('split', [status(esa)], ['148'])).
% 4.42/4.68  thf('160', plain,
% 4.42/4.68      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 4.42/4.68       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D_1))),
% 4.42/4.68      inference('split', [status(esa)], ['148'])).
% 4.42/4.68  thf('161', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 4.42/4.68      inference('sat_resolution*', [status(thm)], ['150', '160'])).
% 4.42/4.68  thf('162', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 4.42/4.68      inference('simpl_trail', [status(thm)], ['159', '161'])).
% 4.42/4.68  thf('163', plain, ($false),
% 4.42/4.68      inference('simplify_reflect-', [status(thm)], ['158', '162'])).
% 4.42/4.68  
% 4.42/4.68  % SZS output end Refutation
% 4.42/4.68  
% 4.42/4.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
