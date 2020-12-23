%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ljel1NQpSq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 6.94s
% Output     : Refutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  215 (2477 expanded)
%              Number of leaves         :   24 ( 742 expanded)
%              Depth                    :   40
%              Number of atoms          : 2039 (21023 expanded)
%              Number of equality atoms :  183 (1268 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t19_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( ( k2_mcart_1 @ A )
            = D )
          | ( ( k2_mcart_1 @ A )
            = E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( ( k2_mcart_1 @ A )
              = D )
            | ( ( k2_mcart_1 @ A )
              = E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X17 @ X19 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X21
        = ( k4_xboole_0 @ X21 @ ( k2_tarski @ X20 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_E ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('38',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k2_mcart_1 @ sk_A ) @ sk_E ) @ ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X25 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('45',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_E ) ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_E ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('65',plain,
    ( ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) )
    | ( r1_tarski @ ( k2_tarski @ ( k2_mcart_1 @ sk_A ) @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) )
    | ( r1_tarski @ ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('69',plain,
    ( ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_E ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('73',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_E ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_D_1 ) )
      | ( r2_hidden @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_E @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('78',plain,
    ( ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) )
    | ( r1_tarski @ ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

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
    ( ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_E @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['69','84'])).

thf('86',plain,
    ( ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('88',plain,
    ( ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('90',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_E )
        = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('95',plain,
    ( ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('97',plain,
    ( ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_D_1 @ ( k2_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['86','97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_E )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('100',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_E ) @ X0 ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_E @ X0 ) )
        = ( k2_mcart_1 @ sk_A ) )
      | ( ( k1_tarski @ sk_D_1 )
        = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','101'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('103',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X33 @ X34 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('104',plain,
    ( ( sk_E
      = ( k2_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D_1 ) @ X0 ) )
      | ( sk_E
        = ( k2_mcart_1 @ sk_A ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_D_1 @ X0 ) )
        = ( k2_mcart_1 @ sk_A ) )
      | ( sk_E
        = ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','106'])).

thf('108',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X33 @ X34 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('109',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_E
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,
    ( ( ( sk_E != sk_E )
      | ( sk_D_1
        = ( k2_mcart_1 @ sk_A ) ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('115',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['110'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('123',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('125',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('133',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C ) @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('135',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_C ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('137',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('142',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('144',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('146',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('148',plain,
    ( ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('150',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
        = ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('155',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('157',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['146','157'])).

thf('159',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('161',plain,
    ( ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('163',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_C )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('168',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('170',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k2_tarski @ sk_B @ ( k1_mcart_1 @ sk_A ) )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['159','170'])).

thf('172',plain,
    ( ( ( k1_tarski @ sk_C )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_C @ X0 ) )
        = ( k1_mcart_1 @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['119','174'])).

thf('176',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X33 @ X34 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('177',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_mcart_1 @ X31 )
        = X30 )
      | ~ ( r2_hidden @ X31 @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ X0 ) )
      | ( sk_C
        = ( k1_mcart_1 @ sk_A ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_B @ X0 ) )
        = ( k1_mcart_1 @ sk_A ) )
      | ( sk_C
        = ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','179'])).

thf('181',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X33 @ X34 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('182',plain,
    ( ( sk_B
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('184',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_B
        = ( k1_mcart_1 @ sk_A ) ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( sk_B
      = ( k1_mcart_1 @ sk_A ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('187',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','116','117','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ljel1NQpSq
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 6.94/7.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.94/7.13  % Solved by: fo/fo7.sh
% 6.94/7.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.94/7.13  % done 5955 iterations in 6.646s
% 6.94/7.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.94/7.13  % SZS output start Refutation
% 6.94/7.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.94/7.13  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 6.94/7.13  thf(sk_E_type, type, sk_E: $i).
% 6.94/7.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.94/7.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.94/7.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.94/7.13  thf(sk_B_type, type, sk_B: $i).
% 6.94/7.13  thf(sk_A_type, type, sk_A: $i).
% 6.94/7.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.94/7.13  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 6.94/7.13  thf(sk_C_type, type, sk_C: $i).
% 6.94/7.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.94/7.13  thf(sk_D_1_type, type, sk_D_1: $i).
% 6.94/7.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.94/7.13  thf(t19_mcart_1, conjecture,
% 6.94/7.13    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.94/7.13     ( ( r2_hidden @
% 6.94/7.13         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 6.94/7.13       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 6.94/7.13         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 6.94/7.13  thf(zf_stmt_0, negated_conjecture,
% 6.94/7.13    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.94/7.13        ( ( r2_hidden @
% 6.94/7.13            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 6.94/7.13          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 6.94/7.13            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 6.94/7.13    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 6.94/7.13  thf('0', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf('1', plain,
% 6.94/7.13      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 6.94/7.13      inference('split', [status(esa)], ['0'])).
% 6.94/7.13  thf('2', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf('3', plain,
% 6.94/7.13      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 6.94/7.13       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 6.94/7.13      inference('split', [status(esa)], ['2'])).
% 6.94/7.13  thf('4', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf('5', plain,
% 6.94/7.13      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 6.94/7.13       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 6.94/7.13      inference('split', [status(esa)], ['4'])).
% 6.94/7.13  thf(t69_enumset1, axiom,
% 6.94/7.13    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.94/7.13  thf('6', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 6.94/7.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.94/7.13  thf(d10_xboole_0, axiom,
% 6.94/7.13    (![A:$i,B:$i]:
% 6.94/7.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.94/7.13  thf('7', plain,
% 6.94/7.13      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 6.94/7.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.94/7.13  thf('8', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 6.94/7.13      inference('simplify', [status(thm)], ['7'])).
% 6.94/7.13  thf(t38_zfmisc_1, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i]:
% 6.94/7.13     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 6.94/7.13       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 6.94/7.13  thf('9', plain,
% 6.94/7.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.94/7.13         ((r2_hidden @ X23 @ X24)
% 6.94/7.13          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 6.94/7.13      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.94/7.13  thf('10', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['8', '9'])).
% 6.94/7.13  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf(l54_zfmisc_1, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i,D:$i]:
% 6.94/7.13     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 6.94/7.13       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 6.94/7.13  thf('13', plain,
% 6.94/7.13      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 6.94/7.13         ((r2_hidden @ (k4_tarski @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X19))
% 6.94/7.13          | ~ (r2_hidden @ X17 @ X19)
% 6.94/7.13          | ~ (r2_hidden @ X15 @ X16))),
% 6.94/7.13      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.94/7.13  thf('14', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X1)
% 6.94/7.13          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 6.94/7.13             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['12', '13'])).
% 6.94/7.13  thf('15', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 6.94/7.13          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['11', '14'])).
% 6.94/7.13  thf('16', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 6.94/7.13          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['11', '14'])).
% 6.94/7.13  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('20', plain,
% 6.94/7.13      ((r2_hidden @ sk_A @ 
% 6.94/7.13        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D_1 @ sk_E)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf(t10_mcart_1, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i]:
% 6.94/7.13     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 6.94/7.13       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 6.94/7.13         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 6.94/7.13  thf('21', plain,
% 6.94/7.13      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.94/7.13         ((r2_hidden @ (k2_mcart_1 @ X27) @ X29)
% 6.94/7.13          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t10_mcart_1])).
% 6.94/7.13  thf('22', plain,
% 6.94/7.13      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_D_1 @ sk_E))),
% 6.94/7.13      inference('sup-', [status(thm)], ['20', '21'])).
% 6.94/7.13  thf(t144_zfmisc_1, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i]:
% 6.94/7.13     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 6.94/7.13          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 6.94/7.13  thf('23', plain,
% 6.94/7.13      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.94/7.13         ((r2_hidden @ X20 @ X21)
% 6.94/7.13          | (r2_hidden @ X22 @ X21)
% 6.94/7.13          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 6.94/7.13      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 6.94/7.13  thf(d5_xboole_0, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i]:
% 6.94/7.13     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 6.94/7.13       ( ![D:$i]:
% 6.94/7.13         ( ( r2_hidden @ D @ C ) <=>
% 6.94/7.13           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 6.94/7.13  thf('24', plain,
% 6.94/7.13      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X4 @ X3)
% 6.94/7.13          | ~ (r2_hidden @ X4 @ X2)
% 6.94/7.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 6.94/7.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 6.94/7.13  thf('25', plain,
% 6.94/7.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X4 @ X2)
% 6.94/7.13          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.94/7.13      inference('simplify', [status(thm)], ['24'])).
% 6.94/7.13  thf('26', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X3 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | (r2_hidden @ X2 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['23', '25'])).
% 6.94/7.13  thf('27', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         ((r2_hidden @ sk_D_1 @ X0)
% 6.94/7.13          | (r2_hidden @ sk_E @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['22', '26'])).
% 6.94/7.13  thf('28', plain,
% 6.94/7.13      (((r2_hidden @ sk_E @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | (r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['19', '27'])).
% 6.94/7.13  thf('29', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 6.94/7.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.94/7.13  thf('30', plain,
% 6.94/7.13      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.94/7.13         ((r2_hidden @ X20 @ X21)
% 6.94/7.13          | (r2_hidden @ X22 @ X21)
% 6.94/7.13          | ((X21) = (k4_xboole_0 @ X21 @ (k2_tarski @ X20 @ X22))))),
% 6.94/7.13      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 6.94/7.13  thf('31', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 6.94/7.13          | (r2_hidden @ X0 @ X1)
% 6.94/7.13          | (r2_hidden @ X0 @ X1))),
% 6.94/7.13      inference('sup+', [status(thm)], ['29', '30'])).
% 6.94/7.13  thf('32', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         ((r2_hidden @ X0 @ X1)
% 6.94/7.13          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['31'])).
% 6.94/7.13  thf('33', plain,
% 6.94/7.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X4 @ X2)
% 6.94/7.13          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 6.94/7.13      inference('simplify', [status(thm)], ['24'])).
% 6.94/7.13  thf('34', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('35', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         ((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 6.94/7.13          | ~ (r2_hidden @ sk_E @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['28', '34'])).
% 6.94/7.13  thf('36', plain,
% 6.94/7.13      (((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_E))
% 6.94/7.13        | (r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['18', '35'])).
% 6.94/7.13  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('38', plain,
% 6.94/7.13      (![X23 : $i, X25 : $i, X26 : $i]:
% 6.94/7.13         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 6.94/7.13          | ~ (r2_hidden @ X25 @ X26)
% 6.94/7.13          | ~ (r2_hidden @ X23 @ X26))),
% 6.94/7.13      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.94/7.13  thf('39', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('40', plain,
% 6.94/7.13      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ (k2_mcart_1 @ sk_A) @ sk_E) @ 
% 6.94/7.13           (k1_tarski @ sk_E)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['36', '39'])).
% 6.94/7.13  thf('41', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 6.94/7.13      inference('simplify', [status(thm)], ['7'])).
% 6.94/7.13  thf('42', plain,
% 6.94/7.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.94/7.13         ((r2_hidden @ X25 @ X24)
% 6.94/7.13          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 6.94/7.13      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.94/7.13  thf('43', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['41', '42'])).
% 6.94/7.13  thf('44', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['8', '9'])).
% 6.94/7.13  thf('45', plain,
% 6.94/7.13      (![X23 : $i, X25 : $i, X26 : $i]:
% 6.94/7.13         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 6.94/7.13          | ~ (r2_hidden @ X25 @ X26)
% 6.94/7.13          | ~ (r2_hidden @ X23 @ X26))),
% 6.94/7.13      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 6.94/7.13  thf('46', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['44', '45'])).
% 6.94/7.13  thf('47', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['43', '46'])).
% 6.94/7.13  thf('48', plain,
% 6.94/7.13      (![X6 : $i, X8 : $i]:
% 6.94/7.13         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 6.94/7.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.94/7.13  thf('49', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X1))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['47', '48'])).
% 6.94/7.13  thf('50', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['43', '46'])).
% 6.94/7.13  thf('51', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.94/7.13      inference('demod', [status(thm)], ['49', '50'])).
% 6.94/7.13  thf('52', plain,
% 6.94/7.13      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ sk_E)))),
% 6.94/7.13      inference('demod', [status(thm)], ['40', '51'])).
% 6.94/7.13  thf('53', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['8', '9'])).
% 6.94/7.13  thf('54', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['44', '45'])).
% 6.94/7.13  thf('55', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['53', '54'])).
% 6.94/7.13  thf('56', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 6.94/7.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.94/7.13  thf('57', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('demod', [status(thm)], ['55', '56'])).
% 6.94/7.13  thf('58', plain,
% 6.94/7.13      (![X6 : $i, X8 : $i]:
% 6.94/7.13         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 6.94/7.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.94/7.13  thf('59', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['57', '58'])).
% 6.94/7.13  thf('60', plain,
% 6.94/7.13      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['52', '59'])).
% 6.94/7.13  thf('61', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('62', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E))
% 6.94/7.13          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 6.94/7.13          | ~ (r2_hidden @ sk_D_1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['60', '61'])).
% 6.94/7.13  thf('63', plain,
% 6.94/7.13      (((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['17', '62'])).
% 6.94/7.13  thf('64', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('65', plain,
% 6.94/7.13      ((((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ (k2_mcart_1 @ sk_A) @ sk_D_1) @ 
% 6.94/7.13           (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['63', '64'])).
% 6.94/7.13  thf('66', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.94/7.13      inference('demod', [status(thm)], ['49', '50'])).
% 6.94/7.13  thf('67', plain,
% 6.94/7.13      ((((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('demod', [status(thm)], ['65', '66'])).
% 6.94/7.13  thf('68', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['57', '58'])).
% 6.94/7.13  thf('69', plain,
% 6.94/7.13      ((((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['67', '68'])).
% 6.94/7.13  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('71', plain,
% 6.94/7.13      ((((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_E))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['67', '68'])).
% 6.94/7.13  thf('72', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['41', '42'])).
% 6.94/7.13  thf('73', plain,
% 6.94/7.13      (((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_E))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup+', [status(thm)], ['71', '72'])).
% 6.94/7.13  thf('74', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('75', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13          | (r2_hidden @ sk_E @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['73', '74'])).
% 6.94/7.13  thf('76', plain,
% 6.94/7.13      (((r2_hidden @ sk_E @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['70', '75'])).
% 6.94/7.13  thf('77', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('78', plain,
% 6.94/7.13      ((((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['76', '77'])).
% 6.94/7.13  thf('79', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.94/7.13      inference('demod', [status(thm)], ['49', '50'])).
% 6.94/7.13  thf('80', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('demod', [status(thm)], ['55', '56'])).
% 6.94/7.13  thf('81', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['79', '80'])).
% 6.94/7.13  thf('82', plain,
% 6.94/7.13      (![X6 : $i, X8 : $i]:
% 6.94/7.13         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 6.94/7.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.94/7.13  thf('83', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['81', '82'])).
% 6.94/7.13  thf('84', plain,
% 6.94/7.13      ((((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k2_tarski @ sk_E @ (k2_mcart_1 @ sk_A))
% 6.94/7.13            = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['78', '83'])).
% 6.94/7.13  thf('85', plain,
% 6.94/7.13      ((((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1)))),
% 6.94/7.13      inference('sup+', [status(thm)], ['69', '84'])).
% 6.94/7.13  thf('86', plain,
% 6.94/7.13      ((((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['85'])).
% 6.94/7.13  thf('87', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('88', plain,
% 6.94/7.13      ((((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) = (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['85'])).
% 6.94/7.13  thf('89', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['41', '42'])).
% 6.94/7.13  thf('90', plain,
% 6.94/7.13      (((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup+', [status(thm)], ['88', '89'])).
% 6.94/7.13  thf('91', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('92', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13          | (r2_hidden @ sk_D_1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['90', '91'])).
% 6.94/7.13  thf('93', plain,
% 6.94/7.13      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['87', '92'])).
% 6.94/7.13  thf('94', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('95', plain,
% 6.94/7.13      ((((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['93', '94'])).
% 6.94/7.13  thf('96', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['81', '82'])).
% 6.94/7.13  thf('97', plain,
% 6.94/7.13      ((((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_D_1 @ (k2_mcart_1 @ sk_A))
% 6.94/7.13            = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['95', '96'])).
% 6.94/7.13  thf('98', plain,
% 6.94/7.13      ((((k1_tarski @ sk_D_1) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup+', [status(thm)], ['86', '97'])).
% 6.94/7.13  thf('99', plain,
% 6.94/7.13      ((((k1_tarski @ sk_E) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_D_1) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['98'])).
% 6.94/7.13  thf(t12_mcart_1, axiom,
% 6.94/7.13    (![A:$i,B:$i,C:$i]:
% 6.94/7.13     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 6.94/7.13       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 6.94/7.13         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 6.94/7.13  thf('100', plain,
% 6.94/7.13      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ X31) = (X30))
% 6.94/7.13          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t12_mcart_1])).
% 6.94/7.13  thf('101', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_E) @ X0))
% 6.94/7.13          | ((k1_tarski @ sk_D_1) = (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 6.94/7.13          | ((k1_mcart_1 @ X1) = (k2_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['99', '100'])).
% 6.94/7.13  thf('102', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ (k4_tarski @ sk_E @ X0)) = (k2_mcart_1 @ sk_A))
% 6.94/7.13          | ((k1_tarski @ sk_D_1) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['16', '101'])).
% 6.94/7.13  thf(t7_mcart_1, axiom,
% 6.94/7.13    (![A:$i,B:$i]:
% 6.94/7.13     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 6.94/7.13       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 6.94/7.13  thf('103', plain,
% 6.94/7.13      (![X33 : $i, X34 : $i]: ((k1_mcart_1 @ (k4_tarski @ X33 @ X34)) = (X33))),
% 6.94/7.13      inference('cnf', [status(esa)], [t7_mcart_1])).
% 6.94/7.13  thf('104', plain,
% 6.94/7.13      ((((sk_E) = (k2_mcart_1 @ sk_A))
% 6.94/7.13        | ((k1_tarski @ sk_D_1) = (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('demod', [status(thm)], ['102', '103'])).
% 6.94/7.13  thf('105', plain,
% 6.94/7.13      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ X31) = (X30))
% 6.94/7.13          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t12_mcart_1])).
% 6.94/7.13  thf('106', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_D_1) @ X0))
% 6.94/7.13          | ((sk_E) = (k2_mcart_1 @ sk_A))
% 6.94/7.13          | ((k1_mcart_1 @ X1) = (k2_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['104', '105'])).
% 6.94/7.13  thf('107', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ (k4_tarski @ sk_D_1 @ X0)) = (k2_mcart_1 @ sk_A))
% 6.94/7.13          | ((sk_E) = (k2_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['15', '106'])).
% 6.94/7.13  thf('108', plain,
% 6.94/7.13      (![X33 : $i, X34 : $i]: ((k1_mcart_1 @ (k4_tarski @ X33 @ X34)) = (X33))),
% 6.94/7.13      inference('cnf', [status(esa)], [t7_mcart_1])).
% 6.94/7.13  thf('109', plain,
% 6.94/7.13      ((((sk_D_1) = (k2_mcart_1 @ sk_A)) | ((sk_E) = (k2_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('demod', [status(thm)], ['107', '108'])).
% 6.94/7.13  thf('110', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf('111', plain,
% 6.94/7.13      ((((k2_mcart_1 @ sk_A) != (sk_E)))
% 6.94/7.13         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 6.94/7.13      inference('split', [status(esa)], ['110'])).
% 6.94/7.13  thf('112', plain,
% 6.94/7.13      (((((sk_E) != (sk_E)) | ((sk_D_1) = (k2_mcart_1 @ sk_A))))
% 6.94/7.13         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['109', '111'])).
% 6.94/7.13  thf('113', plain,
% 6.94/7.13      ((((sk_D_1) = (k2_mcart_1 @ sk_A)))
% 6.94/7.13         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['112'])).
% 6.94/7.13  thf('114', plain,
% 6.94/7.13      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 6.94/7.13         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 6.94/7.13      inference('split', [status(esa)], ['2'])).
% 6.94/7.13  thf('115', plain,
% 6.94/7.13      ((((sk_D_1) != (sk_D_1)))
% 6.94/7.13         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))) & 
% 6.94/7.13             ~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['113', '114'])).
% 6.94/7.13  thf('116', plain,
% 6.94/7.13      ((((k2_mcart_1 @ sk_A) = (sk_E))) | (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 6.94/7.13      inference('simplify', [status(thm)], ['115'])).
% 6.94/7.13  thf('117', plain,
% 6.94/7.13      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 6.94/7.13      inference('split', [status(esa)], ['110'])).
% 6.94/7.13  thf('118', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 6.94/7.13          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['11', '14'])).
% 6.94/7.13  thf('119', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 6.94/7.13          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['11', '14'])).
% 6.94/7.13  thf('120', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('121', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('122', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('123', plain,
% 6.94/7.13      ((r2_hidden @ sk_A @ 
% 6.94/7.13        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D_1 @ sk_E)))),
% 6.94/7.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.94/7.13  thf('124', plain,
% 6.94/7.13      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.94/7.13         ((r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 6.94/7.13          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t10_mcart_1])).
% 6.94/7.13  thf('125', plain,
% 6.94/7.13      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 6.94/7.13      inference('sup-', [status(thm)], ['123', '124'])).
% 6.94/7.13  thf('126', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X3 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | (r2_hidden @ X2 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['23', '25'])).
% 6.94/7.13  thf('127', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         ((r2_hidden @ sk_B @ X0)
% 6.94/7.13          | (r2_hidden @ sk_C @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['125', '126'])).
% 6.94/7.13  thf('128', plain,
% 6.94/7.13      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['122', '127'])).
% 6.94/7.13  thf('129', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('130', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 6.94/7.13          | ~ (r2_hidden @ sk_C @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['128', '129'])).
% 6.94/7.13  thf('131', plain,
% 6.94/7.13      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 6.94/7.13        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['121', '130'])).
% 6.94/7.13  thf('132', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('133', plain,
% 6.94/7.13      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_C) @ 
% 6.94/7.13           (k1_tarski @ sk_C)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['131', '132'])).
% 6.94/7.13  thf('134', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.94/7.13      inference('demod', [status(thm)], ['49', '50'])).
% 6.94/7.13  thf('135', plain,
% 6.94/7.13      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ sk_C)))),
% 6.94/7.13      inference('demod', [status(thm)], ['133', '134'])).
% 6.94/7.13  thf('136', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['57', '58'])).
% 6.94/7.13  thf('137', plain,
% 6.94/7.13      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['135', '136'])).
% 6.94/7.13  thf('138', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('139', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 6.94/7.13          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 6.94/7.13          | ~ (r2_hidden @ sk_B @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['137', '138'])).
% 6.94/7.13  thf('140', plain,
% 6.94/7.13      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 6.94/7.13        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['120', '139'])).
% 6.94/7.13  thf('141', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('142', plain,
% 6.94/7.13      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ (k1_mcart_1 @ sk_A) @ sk_B) @ 
% 6.94/7.13           (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['140', '141'])).
% 6.94/7.13  thf('143', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 6.94/7.13      inference('demod', [status(thm)], ['49', '50'])).
% 6.94/7.13  thf('144', plain,
% 6.94/7.13      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('demod', [status(thm)], ['142', '143'])).
% 6.94/7.13  thf('145', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['57', '58'])).
% 6.94/7.13  thf('146', plain,
% 6.94/7.13      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['144', '145'])).
% 6.94/7.13  thf('147', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('148', plain,
% 6.94/7.13      ((((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_C))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['144', '145'])).
% 6.94/7.13  thf('149', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['41', '42'])).
% 6.94/7.13  thf('150', plain,
% 6.94/7.13      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup+', [status(thm)], ['148', '149'])).
% 6.94/7.13  thf('151', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('152', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13          | (r2_hidden @ sk_C @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['150', '151'])).
% 6.94/7.13  thf('153', plain,
% 6.94/7.13      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['147', '152'])).
% 6.94/7.13  thf('154', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('155', plain,
% 6.94/7.13      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['153', '154'])).
% 6.94/7.13  thf('156', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['81', '82'])).
% 6.94/7.13  thf('157', plain,
% 6.94/7.13      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13        | ((k2_tarski @ sk_C @ (k1_mcart_1 @ sk_A))
% 6.94/7.13            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['155', '156'])).
% 6.94/7.13  thf('158', plain,
% 6.94/7.13      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B)))),
% 6.94/7.13      inference('sup+', [status(thm)], ['146', '157'])).
% 6.94/7.13  thf('159', plain,
% 6.94/7.13      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['158'])).
% 6.94/7.13  thf('160', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.94/7.13      inference('sup+', [status(thm)], ['6', '10'])).
% 6.94/7.13  thf('161', plain,
% 6.94/7.13      ((((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) = (k1_tarski @ sk_B))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['158'])).
% 6.94/7.13  thf('162', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['41', '42'])).
% 6.94/7.13  thf('163', plain,
% 6.94/7.13      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup+', [status(thm)], ['161', '162'])).
% 6.94/7.13  thf('164', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X2 @ X0)
% 6.94/7.13          | (r2_hidden @ X1 @ X0)
% 6.94/7.13          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['32', '33'])).
% 6.94/7.13  thf('165', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13          | (r2_hidden @ sk_B @ X0)
% 6.94/7.13          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 6.94/7.13      inference('sup-', [status(thm)], ['163', '164'])).
% 6.94/7.13  thf('166', plain,
% 6.94/7.13      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['160', '165'])).
% 6.94/7.13  thf('167', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 6.94/7.13          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['37', '38'])).
% 6.94/7.13  thf('168', plain,
% 6.94/7.13      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | (r1_tarski @ (k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A)) @ 
% 6.94/7.13           (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['166', '167'])).
% 6.94/7.13  thf('169', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 6.94/7.13          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X0)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['81', '82'])).
% 6.94/7.13  thf('170', plain,
% 6.94/7.13      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k2_tarski @ sk_B @ (k1_mcart_1 @ sk_A))
% 6.94/7.13            = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['168', '169'])).
% 6.94/7.13  thf('171', plain,
% 6.94/7.13      ((((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup+', [status(thm)], ['159', '170'])).
% 6.94/7.13  thf('172', plain,
% 6.94/7.13      ((((k1_tarski @ sk_C) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['171'])).
% 6.94/7.13  thf('173', plain,
% 6.94/7.13      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ X31) = (X30))
% 6.94/7.13          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t12_mcart_1])).
% 6.94/7.13  thf('174', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ X0))
% 6.94/7.13          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 6.94/7.13          | ((k1_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['172', '173'])).
% 6.94/7.13  thf('175', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ (k4_tarski @ sk_C @ X0)) = (k1_mcart_1 @ sk_A))
% 6.94/7.13          | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['119', '174'])).
% 6.94/7.13  thf('176', plain,
% 6.94/7.13      (![X33 : $i, X34 : $i]: ((k1_mcart_1 @ (k4_tarski @ X33 @ X34)) = (X33))),
% 6.94/7.13      inference('cnf', [status(esa)], [t7_mcart_1])).
% 6.94/7.13  thf('177', plain,
% 6.94/7.13      ((((sk_C) = (k1_mcart_1 @ sk_A))
% 6.94/7.13        | ((k1_tarski @ sk_B) = (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 6.94/7.13      inference('demod', [status(thm)], ['175', '176'])).
% 6.94/7.13  thf('178', plain,
% 6.94/7.13      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ X31) = (X30))
% 6.94/7.13          | ~ (r2_hidden @ X31 @ (k2_zfmisc_1 @ (k1_tarski @ X30) @ X32)))),
% 6.94/7.13      inference('cnf', [status(esa)], [t12_mcart_1])).
% 6.94/7.13  thf('179', plain,
% 6.94/7.13      (![X0 : $i, X1 : $i]:
% 6.94/7.13         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ X0))
% 6.94/7.13          | ((sk_C) = (k1_mcart_1 @ sk_A))
% 6.94/7.13          | ((k1_mcart_1 @ X1) = (k1_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['177', '178'])).
% 6.94/7.13  thf('180', plain,
% 6.94/7.13      (![X0 : $i]:
% 6.94/7.13         (((k1_mcart_1 @ (k4_tarski @ sk_B @ X0)) = (k1_mcart_1 @ sk_A))
% 6.94/7.13          | ((sk_C) = (k1_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('sup-', [status(thm)], ['118', '179'])).
% 6.94/7.13  thf('181', plain,
% 6.94/7.13      (![X33 : $i, X34 : $i]: ((k1_mcart_1 @ (k4_tarski @ X33 @ X34)) = (X33))),
% 6.94/7.13      inference('cnf', [status(esa)], [t7_mcart_1])).
% 6.94/7.13  thf('182', plain,
% 6.94/7.13      ((((sk_B) = (k1_mcart_1 @ sk_A)) | ((sk_C) = (k1_mcart_1 @ sk_A)))),
% 6.94/7.13      inference('demod', [status(thm)], ['180', '181'])).
% 6.94/7.13  thf('183', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 6.94/7.13         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 6.94/7.13      inference('split', [status(esa)], ['4'])).
% 6.94/7.13  thf('184', plain,
% 6.94/7.13      (((((sk_C) != (sk_C)) | ((sk_B) = (k1_mcart_1 @ sk_A))))
% 6.94/7.13         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['182', '183'])).
% 6.94/7.13  thf('185', plain,
% 6.94/7.13      ((((sk_B) = (k1_mcart_1 @ sk_A))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 6.94/7.13      inference('simplify', [status(thm)], ['184'])).
% 6.94/7.13  thf('186', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 6.94/7.13         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 6.94/7.13      inference('split', [status(esa)], ['2'])).
% 6.94/7.13  thf('187', plain,
% 6.94/7.13      ((((sk_B) != (sk_B)))
% 6.94/7.13         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 6.94/7.13             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 6.94/7.13      inference('sup-', [status(thm)], ['185', '186'])).
% 6.94/7.13  thf('188', plain,
% 6.94/7.13      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 6.94/7.13      inference('simplify', [status(thm)], ['187'])).
% 6.94/7.13  thf('189', plain, ($false),
% 6.94/7.13      inference('sat_resolution*', [status(thm)],
% 6.94/7.13                ['1', '3', '5', '116', '117', '188'])).
% 6.94/7.13  
% 6.94/7.13  % SZS output end Refutation
% 6.94/7.13  
% 6.94/7.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
