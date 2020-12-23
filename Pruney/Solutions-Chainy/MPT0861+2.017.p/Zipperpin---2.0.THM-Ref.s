%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gQgEgnj0r6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:53 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 448 expanded)
%              Number of leaves         :   18 ( 124 expanded)
%              Depth                    :   23
%              Number of atoms          :  874 (5022 expanded)
%              Number of equality atoms :   56 ( 451 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X13
        = ( k4_xboole_0 @ X13 @ ( k2_tarski @ X12 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('24',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('26',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ( X13
        = ( k4_xboole_0 @ X13 @ ( k2_tarski @ X12 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X18 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_mcart_1 @ X22 )
        = X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ ( k1_tarski @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('45',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['42','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k4_xboole_0 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('63',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('68',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('70',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('71',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['49','70'])).

thf('72',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('75',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('77',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['42','51'])).

thf('79',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['57'])).

thf('81',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X18 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gQgEgnj0r6
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 392 iterations in 0.243s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.47/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.69  thf(t17_mcart_1, conjecture,
% 0.47/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69     ( ( r2_hidden @
% 0.47/0.69         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.47/0.69       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.47/0.69         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.69        ( ( r2_hidden @
% 0.47/0.69            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.47/0.69          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.47/0.69            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      ((r2_hidden @ sk_A @ 
% 0.47/0.69        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t10_mcart_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.47/0.69       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.47/0.69         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.69         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.47/0.69          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.47/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf(t144_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.47/0.69          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.69         ((r2_hidden @ X12 @ X13)
% 0.47/0.69          | (r2_hidden @ X14 @ X13)
% 0.47/0.69          | ((X13) = (k4_xboole_0 @ X13 @ (k2_tarski @ X12 @ X14))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.47/0.69  thf(d5_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.69       ( ![D:$i]:
% 0.47/0.69         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.69           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X4 @ X3)
% 0.47/0.69          | ~ (r2_hidden @ X4 @ X2)
% 0.47/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf('7', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X3 @ X0)
% 0.47/0.69          | (r2_hidden @ X1 @ X0)
% 0.47/0.69          | (r2_hidden @ X2 @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['4', '6'])).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ X0)
% 0.47/0.69          | (r2_hidden @ sk_C @ X0)
% 0.47/0.69          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['3', '7'])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k2_tarski @ sk_B @ sk_C))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['2', '8'])).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | (r2_hidden @ X0 @ X3)
% 0.47/0.69          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.69  thf('12', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C))
% 0.47/0.69          | (r2_hidden @ sk_C @ X0)
% 0.47/0.69          | (r2_hidden @ sk_C @ (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['9', '11'])).
% 0.47/0.69  thf(t64_zfmisc_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.47/0.69       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.47/0.69  thf('13', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.69         (((X15) != (X17))
% 0.47/0.69          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('15', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k2_tarski @ sk_B @ sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['12', '14'])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.47/0.69          | (r2_hidden @ sk_B @ X0)
% 0.47/0.69          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('19', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.47/0.69        | (r2_hidden @ sk_C @ (k1_tarski @ sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.69  thf('20', plain,
% 0.47/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf('21', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.47/0.69          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.47/0.69             (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf('25', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ X0)
% 0.47/0.69          | (r2_hidden @ sk_C @ X0)
% 0.47/0.69          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['3', '7'])).
% 0.47/0.69  thf('26', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.69  thf(t69_enumset1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.69  thf('27', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.47/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.69  thf('28', plain,
% 0.47/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.69         ((r2_hidden @ X12 @ X13)
% 0.47/0.69          | (r2_hidden @ X14 @ X13)
% 0.47/0.69          | ((X13) = (k4_xboole_0 @ X13 @ (k2_tarski @ X12 @ X14))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.47/0.69  thf('29', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.47/0.69          | (r2_hidden @ X0 @ X1)
% 0.47/0.69          | (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.47/0.69  thf('30', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ X1)
% 0.47/0.69          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.47/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.47/0.69  thf('31', plain,
% 0.47/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf('32', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X2 @ X0)
% 0.47/0.69          | (r2_hidden @ X1 @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('33', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.47/0.69          | ~ (r2_hidden @ sk_C @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['26', '32'])).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.47/0.69        | (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['19', '33'])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.47/0.69         ((r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X18)))
% 0.47/0.69          | ((X15) = (X18))
% 0.47/0.69          | ~ (r2_hidden @ X15 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_mcart_1 @ sk_A) = (X0))
% 0.47/0.69          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.47/0.69             (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ X0))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_mcart_1 @ sk_A) = (X0))
% 0.47/0.69          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.47/0.69        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['34', '39'])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.47/0.69         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.47/0.69      inference('split', [status(esa)], ['41'])).
% 0.47/0.69  thf('43', plain,
% 0.47/0.69      ((r2_hidden @ sk_A @ 
% 0.47/0.69        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(t13_mcart_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.47/0.69       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.47/0.69         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.47/0.69  thf('44', plain,
% 0.47/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.69         (((k2_mcart_1 @ X22) = (X24))
% 0.47/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ (k1_tarski @ X24))))),
% 0.47/0.69      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.47/0.69  thf('45', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.47/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.47/0.69         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.47/0.69      inference('split', [status(esa)], ['46'])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['45', '47'])).
% 0.47/0.69  thf('49', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.47/0.69       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.47/0.69      inference('split', [status(esa)], ['41'])).
% 0.47/0.69  thf('51', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.47/0.69  thf('52', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['42', '51'])).
% 0.47/0.69  thf('53', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['40', '52'])).
% 0.47/0.69  thf('54', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.69  thf('55', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.47/0.69          | (r2_hidden @ sk_B @ X0)
% 0.47/0.69          | (r2_hidden @ sk_B @ 
% 0.47/0.69             (k4_xboole_0 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.69  thf('56', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('57', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.69  thf('58', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))),
% 0.47/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.69  thf('59', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.69  thf('60', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.47/0.69          | (r2_hidden @ X0 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.69  thf('61', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69          | (r2_hidden @ sk_C @ X0)
% 0.47/0.69          | (r2_hidden @ sk_C @ 
% 0.47/0.69             (k4_xboole_0 @ (k1_tarski @ (k1_mcart_1 @ sk_A)) @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.69  thf('62', plain,
% 0.47/0.69      (![X16 : $i, X17 : $i]:
% 0.47/0.69         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.69  thf('63', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.47/0.69  thf('64', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X2 @ X0)
% 0.47/0.69          | (r2_hidden @ X1 @ X0)
% 0.47/0.69          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.69  thf('65', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.47/0.69          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.47/0.69          | ~ (r2_hidden @ sk_B @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.69  thf('66', plain,
% 0.47/0.69      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 0.47/0.69        | (r2_hidden @ sk_C @ (k1_tarski @ sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['58', '65'])).
% 0.47/0.69  thf('67', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_mcart_1 @ sk_A) = (X0))
% 0.47/0.69          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('68', plain,
% 0.47/0.69      (((r2_hidden @ sk_C @ (k1_tarski @ sk_C))
% 0.47/0.69        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.47/0.69  thf('69', plain,
% 0.47/0.69      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.47/0.69         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.47/0.69      inference('split', [status(esa)], ['46'])).
% 0.47/0.69  thf('70', plain,
% 0.47/0.69      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.47/0.69       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.47/0.69      inference('split', [status(esa)], ['46'])).
% 0.47/0.69  thf('71', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.47/0.69      inference('sat_resolution*', [status(thm)], ['49', '70'])).
% 0.47/0.69  thf('72', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.47/0.69  thf('73', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_C))),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['68', '72'])).
% 0.47/0.69  thf('74', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.47/0.69          | ~ (r2_hidden @ sk_C @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['26', '32'])).
% 0.47/0.69  thf('75', plain,
% 0.47/0.69      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))
% 0.47/0.69        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['73', '74'])).
% 0.47/0.69  thf('76', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k1_mcart_1 @ sk_A) = (X0))
% 0.47/0.69          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.69  thf('77', plain,
% 0.47/0.69      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.47/0.69        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.69  thf('78', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['42', '51'])).
% 0.47/0.69  thf('79', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.47/0.69  thf('80', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_B))),
% 0.47/0.69      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.69  thf('81', plain,
% 0.47/0.69      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.47/0.69         ((r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X18)))
% 0.47/0.69          | ((X15) = (X18))
% 0.47/0.69          | ~ (r2_hidden @ X15 @ X16))),
% 0.47/0.69      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.47/0.69  thf('82', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((sk_B) = (X0))
% 0.47/0.69          | (r2_hidden @ sk_B @ 
% 0.47/0.69             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['80', '81'])).
% 0.47/0.69  thf('83', plain,
% 0.47/0.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.47/0.69          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.69  thf('84', plain,
% 0.47/0.69      (![X0 : $i]: (((sk_B) = (X0)) | ~ (r2_hidden @ sk_B @ (k1_tarski @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.69  thf('85', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.47/0.69      inference('sup-', [status(thm)], ['79', '84'])).
% 0.47/0.69  thf('86', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.47/0.69      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.47/0.69  thf('87', plain, ($false),
% 0.47/0.69      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
