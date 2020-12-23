%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bypaVgg7Hh

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:20 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 604 expanded)
%              Number of leaves         :   22 ( 184 expanded)
%              Depth                    :   23
%              Number of atoms          :  700 (5919 expanded)
%              Number of equality atoms :  126 (1070 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( X42 = X39 )
      | ( X41
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('21',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X72: $i,X74: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X72 ) @ X74 )
      | ~ ( r2_hidden @ X72 @ X74 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X22: $i] :
      ( ( X20 = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ ( sk_B @ sk_C_2 ) ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf('28',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ ( sk_B @ sk_C_2 ) ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_2
      = ( k1_tarski @ ( sk_B @ sk_C_2 ) ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_C_2
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('35',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('50',plain,(
    ! [X20: $i,X22: $i] :
      ( ( X20 = X22 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('58',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','36','59'])).

thf('61',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','60'])).

thf('62',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','61'])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('64',plain,
    ( ( sk_B_1 = sk_C_2 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','61'])).

thf('66',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('67',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('70',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B_1 = sk_C_2 ),
    inference(simpl_trail,[status(thm)],['64','70'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('72',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('75',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('76',plain,(
    ! [X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','71','72','77'])).

thf('79',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('80',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('81',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bypaVgg7Hh
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 632 iterations in 0.318s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.74  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.52/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.52/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.74  thf(t43_zfmisc_1, conjecture,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.52/0.74          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.74          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.74          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.74        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.52/0.74             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.74             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.74             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.52/0.74  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(l51_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      (![X75 : $i, X76 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.74  thf(t7_xboole_0, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X19 : $i]:
% 0.52/0.74         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.74  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      (![X75 : $i, X76 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      (![X75 : $i, X76 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 0.52/0.74           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 0.52/0.74      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.52/0.74  thf(t7_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('9', plain,
% 0.52/0.74      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      (![X75 : $i, X76 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('11', plain,
% 0.52/0.74      (![X31 : $i, X32 : $i]:
% 0.52/0.74         (r1_tarski @ X31 @ (k3_tarski @ (k2_tarski @ X31 @ X32)))),
% 0.52/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['8', '11'])).
% 0.52/0.74  thf('13', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup+', [status(thm)], ['4', '12'])).
% 0.52/0.74  thf(d3_tarski, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.74  thf('14', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X4 @ X5)
% 0.52/0.74          | (r2_hidden @ X4 @ X6)
% 0.52/0.74          | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.52/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('16', plain,
% 0.52/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.52/0.74        | (r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['3', '15'])).
% 0.52/0.74  thf(d1_tarski, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.52/0.74  thf('17', plain,
% 0.52/0.74      (![X39 : $i, X41 : $i, X42 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X42 @ X41)
% 0.52/0.74          | ((X42) = (X39))
% 0.52/0.74          | ((X41) != (k1_tarski @ X39)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d1_tarski])).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      (![X39 : $i, X42 : $i]:
% 0.52/0.74         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.74  thf('19', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B @ sk_C_2) = (sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.74  thf('20', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B @ sk_C_2) = (sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.74  thf('21', plain,
% 0.52/0.74      (![X19 : $i]:
% 0.52/0.74         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.74  thf(l1_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.52/0.74  thf('22', plain,
% 0.52/0.74      (![X72 : $i, X74 : $i]:
% 0.52/0.74         ((r1_tarski @ (k1_tarski @ X72) @ X74) | ~ (r2_hidden @ X72 @ X74))),
% 0.52/0.74      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.74  thf(d10_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      (![X20 : $i, X22 : $i]:
% 0.52/0.74         (((X20) = (X22))
% 0.52/0.74          | ~ (r1_tarski @ X22 @ X20)
% 0.52/0.74          | ~ (r1_tarski @ X20 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('25', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((X0) = (k1_xboole_0))
% 0.52/0.74          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.52/0.74          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.74  thf('26', plain,
% 0.52/0.74      ((~ (r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.52/0.74        | ((sk_C_2) = (k1_xboole_0))
% 0.52/0.74        | ((sk_C_2) = (k1_tarski @ (sk_B @ sk_C_2)))
% 0.52/0.74        | ((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['20', '25'])).
% 0.52/0.74  thf('27', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup+', [status(thm)], ['4', '12'])).
% 0.52/0.74  thf('28', plain,
% 0.52/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.52/0.74        | ((sk_C_2) = (k1_tarski @ (sk_B @ sk_C_2)))
% 0.52/0.74        | ((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.74  thf('29', plain,
% 0.52/0.74      ((((sk_C_2) = (k1_tarski @ (sk_B @ sk_C_2))) | ((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      ((((sk_C_2) = (k1_tarski @ sk_A))
% 0.52/0.74        | ((sk_C_2) = (k1_xboole_0))
% 0.52/0.74        | ((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['19', '29'])).
% 0.52/0.74  thf('31', plain,
% 0.52/0.74      ((((sk_C_2) = (k1_xboole_0)) | ((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['30'])).
% 0.52/0.74  thf('32', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.52/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('split', [status(esa)], ['32'])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('split', [status(esa)], ['32'])).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('36', plain,
% 0.52/0.74      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.52/0.74       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('split', [status(esa)], ['35'])).
% 0.52/0.74  thf('37', plain,
% 0.52/0.74      (![X19 : $i]:
% 0.52/0.74         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 0.52/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.52/0.74  thf('38', plain,
% 0.52/0.74      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_2)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.74  thf('39', plain,
% 0.52/0.74      (![X31 : $i, X32 : $i]:
% 0.52/0.74         (r1_tarski @ X31 @ (k3_tarski @ (k2_tarski @ X31 @ X32)))),
% 0.52/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.74  thf('40', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.74  thf('41', plain,
% 0.52/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X4 @ X5)
% 0.52/0.74          | (r2_hidden @ X4 @ X6)
% 0.52/0.74          | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.74  thf('42', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.74  thf('43', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['37', '42'])).
% 0.52/0.74  thf('44', plain,
% 0.52/0.74      (![X39 : $i, X42 : $i]:
% 0.52/0.74         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.74  thf('45', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['43', '44'])).
% 0.52/0.74  thf('46', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.74  thf('47', plain,
% 0.52/0.74      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.52/0.74        | ((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['45', '46'])).
% 0.52/0.74  thf('48', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.52/0.74      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.74  thf('49', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.74  thf('50', plain,
% 0.52/0.74      (![X20 : $i, X22 : $i]:
% 0.52/0.74         (((X20) = (X22))
% 0.52/0.74          | ~ (r1_tarski @ X22 @ X20)
% 0.52/0.74          | ~ (r1_tarski @ X20 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('51', plain,
% 0.52/0.74      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.52/0.74        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.52/0.74  thf('52', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['48', '51'])).
% 0.52/0.74  thf('53', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('54', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.52/0.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('split', [status(esa)], ['53'])).
% 0.52/0.74  thf('55', plain,
% 0.52/0.74      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.52/0.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['52', '54'])).
% 0.52/0.74  thf('56', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.74  thf('57', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.52/0.74      inference('split', [status(esa)], ['32'])).
% 0.52/0.74  thf('58', plain,
% 0.52/0.74      ((((sk_B_1) != (sk_B_1)))
% 0.52/0.74         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.52/0.74             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.74  thf('59', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.52/0.74  thf('60', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['34', '36', '59'])).
% 0.52/0.74  thf('61', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['33', '60'])).
% 0.52/0.74  thf('62', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['31', '61'])).
% 0.52/0.74  thf('63', plain,
% 0.52/0.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.74  thf('64', plain,
% 0.52/0.74      ((((sk_B_1) = (sk_C_2))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('sup+', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('65', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['31', '61'])).
% 0.52/0.74  thf('66', plain,
% 0.52/0.74      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.52/0.74      inference('split', [status(esa)], ['53'])).
% 0.52/0.74  thf('67', plain,
% 0.52/0.74      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.52/0.74  thf('68', plain, ((((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['67'])).
% 0.52/0.74  thf('69', plain,
% 0.52/0.74      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.74      inference('split', [status(esa)], ['53'])).
% 0.52/0.74  thf('70', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.52/0.74  thf('71', plain, (((sk_B_1) = (sk_C_2))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['64', '70'])).
% 0.52/0.74  thf(t69_enumset1, axiom,
% 0.52/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.74  thf('72', plain,
% 0.52/0.74      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf('73', plain,
% 0.52/0.74      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.52/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.74  thf(idempotence_k2_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.74  thf('74', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ X17) = (X17))),
% 0.52/0.74      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.52/0.74  thf('75', plain,
% 0.52/0.74      (![X75 : $i, X76 : $i]:
% 0.52/0.74         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.52/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.74  thf('76', plain,
% 0.52/0.74      (![X17 : $i]: ((k3_tarski @ (k2_tarski @ X17 @ X17)) = (X17))),
% 0.52/0.74      inference('demod', [status(thm)], ['74', '75'])).
% 0.52/0.74  thf('77', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['73', '76'])).
% 0.52/0.74  thf('78', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.52/0.74      inference('demod', [status(thm)], ['2', '71', '72', '77'])).
% 0.52/0.74  thf('79', plain,
% 0.52/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.52/0.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('split', [status(esa)], ['53'])).
% 0.52/0.74  thf('80', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.52/0.74  thf('81', plain, (((sk_B_1) != (k1_tarski @ sk_A))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.52/0.74  thf('82', plain, ($false),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['78', '81'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
