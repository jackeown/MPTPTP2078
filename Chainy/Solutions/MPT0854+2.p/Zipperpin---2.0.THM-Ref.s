%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0854+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D0Weqlz1Ht

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 38.98s
% Output     : Refutation 38.98s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 483 expanded)
%              Number of leaves         :   17 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  352 (4274 expanded)
%              Number of equality atoms :   31 ( 367 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_72_type,type,(
    sk_B_72: $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_D_11_type,type,(
    sk_D_11: $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(t10_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A @ B ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ ( D @ E ) )
           != A ) ) )).

thf('3',plain,(
    ! [X1015: $i,X1016: $i,X1017: $i] :
      ( ( ( k4_tarski @ ( sk_D_11 @ X1015 @ ( sk_E_3 @ X1015 ) ) )
        = X1015 )
      | ~ ( r2_hidden @ ( X1015 @ ( k2_zfmisc_1 @ ( X1016 @ X1017 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X3871: $i,X3872: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3871 @ X3872 ) ) )
      = X3871 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( sk_D_11 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( sk_E_3 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['4','7'])).

thf('10',plain,(
    ! [X3871: $i,X3873: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3871 @ X3873 ) ) )
      = X3873 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( sk_E_3 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['8','11'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ ( A @ B ) )
        = ( k4_tarski @ ( C @ D ) ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('14',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1285 = X1284 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('15',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['14'])).

thf('16',plain,
    ( ( '#_fresh_sk2' @ sk_A_14 )
    = ( k1_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1287 = X1286 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('19',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['18'])).

thf('20',plain,
    ( ( '#_fresh_sk3' @ sk_A_14 )
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_A_14 @ sk_C_93 ) )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference(demod,[status(thm)],['1','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['12','16'])).

thf('24',plain,
    ( ( '#_fresh_sk3' @ sk_A_14 )
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('25',plain,
    ( ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['23','24'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ ( k2_zfmisc_1 @ ( C @ D ) ) ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ D ) ) ) ) )).

thf('26',plain,(
    ! [X1062: $i,X1063: $i,X1064: $i,X1065: $i] :
      ( ( r2_hidden @ ( X1062 @ X1063 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X1062 @ X1064 ) @ ( k2_zfmisc_1 @ ( X1063 @ X1065 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( '#_fresh_sk2' @ sk_A_14 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( '#_fresh_sk2' @ sk_A_14 @ sk_B_72 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( '#_fresh_sk2' @ sk_A_14 )
    = ( k1_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( '#_fresh_sk2' @ sk_A_14 @ sk_B_72 ) )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A_14 @ sk_B_72 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A_14 @ sk_C_93 ) ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ ( '#_fresh_sk3' @ sk_A_14 @ sk_C_93 ) ) ),
    inference(simpl_trail,[status(thm)],['21','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_72 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) )
    = sk_A_14 ),
    inference(demod,[status(thm)],['23','24'])).

thf('38',plain,(
    ! [X1062: $i,X1063: $i,X1064: $i,X1065: $i] :
      ( ( r2_hidden @ ( X1064 @ X1065 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X1062 @ X1064 ) @ ( k2_zfmisc_1 @ ( X1063 @ X1065 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( '#_fresh_sk3' @ sk_A_14 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( '#_fresh_sk3' @ sk_A_14 @ sk_C_93 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['35','40'])).

%------------------------------------------------------------------------------
