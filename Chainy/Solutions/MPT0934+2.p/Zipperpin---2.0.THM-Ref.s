%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0934+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLqxXvVybb

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 14.26s
% Output     : Refutation 14.26s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 524 expanded)
%              Number of leaves         :   19 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  456 (5981 expanded)
%              Number of equality atoms :   63 ( 695 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_38_type,type,(
    sk_D_38: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_B_80_type,type,(
    sk_B_80: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_C_26_type,type,(
    sk_C_26: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t95_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ A ) )
             => ( ( ( ( k1_mcart_1 @ B )
                    = ( k1_mcart_1 @ C ) )
                  & ( ( k2_mcart_1 @ B )
                    = ( k2_mcart_1 @ C ) ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_relat_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ ( B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ A ) )
               => ( ( ( ( k1_mcart_1 @ B )
                      = ( k1_mcart_1 @ C ) )
                    & ( ( k2_mcart_1 @ B )
                      = ( k2_mcart_1 @ C ) ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_80 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A_14 )
    | ( r2_hidden @ ( sk_B_80 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ ( sk_B_80 @ sk_A_14 ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ ( B @ A ) )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ ( C @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X2089: $i,X2090: $i] :
      ( ( X2089
        = ( k4_tarski @ ( sk_C_26 @ X2089 @ ( sk_D_38 @ X2089 ) ) ) )
      | ~ ( r2_hidden @ ( X2089 @ X2090 ) )
      | ~ ( v1_relat_1 @ X2090 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( sk_B_80
      = ( k4_tarski @ ( sk_C_26 @ sk_B_80 @ ( sk_D_38 @ sk_B_80 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_B_80
    = ( k4_tarski @ ( sk_C_26 @ sk_B_80 @ ( sk_D_38 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( sk_B_80
    = ( k4_tarski @ ( sk_C_26 @ sk_B_80 @ ( sk_D_38 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ ( A @ B ) )
        = ( k4_tarski @ ( C @ D ) ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('10',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1285 = X1284 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('11',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['10'])).

thf('12',plain,
    ( ( '#_fresh_sk2' @ sk_B_80 )
    = ( sk_C_26 @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_B_80
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( sk_D_38 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('14',plain,
    ( sk_B_80
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( sk_D_38 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['8','12'])).

thf('15',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1287 = X1286 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('16',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['15'])).

thf('17',plain,
    ( ( '#_fresh_sk3' @ sk_B_80 )
    = ( sk_D_38 @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,
    ( sk_B_80
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( '#_fresh_sk3' @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_C_93 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_A_14 )
    | ( r2_hidden @ ( sk_C_93 @ sk_A_14 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_C_93 @ sk_A_14 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2089: $i,X2090: $i] :
      ( ( X2089
        = ( k4_tarski @ ( sk_C_26 @ X2089 @ ( sk_D_38 @ X2089 ) ) ) )
      | ~ ( r2_hidden @ ( X2089 @ X2090 ) )
      | ~ ( v1_relat_1 @ X2090 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_A_14 )
    | ( sk_C_93
      = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['10'])).

thf('30',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('33',plain,(
    ! [X4321: $i,X4323: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4321 @ X4323 ) ) )
      = X4323 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('34',plain,
    ( ( k2_mcart_1 @ sk_C_93 )
    = ( sk_D_38 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_mcart_1 @ sk_B_80 )
    = ( k2_mcart_1 @ sk_C_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_mcart_1 @ sk_B_80 )
    = ( sk_D_38 @ sk_C_93 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_C_93 @ ( k2_mcart_1 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_C_93 @ ( k2_mcart_1 @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('39',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['15'])).

thf('40',plain,
    ( ( '#_fresh_sk3' @ sk_C_93 )
    = ( k2_mcart_1 @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_C_93 @ ( '#_fresh_sk3' @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( sk_B_80
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( '#_fresh_sk3' @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('43',plain,(
    ! [X4321: $i,X4322: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4321 @ X4322 ) ) )
      = X4321 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('44',plain,
    ( ( k1_mcart_1 @ sk_B_80 )
    = ( '#_fresh_sk2' @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('46',plain,(
    ! [X4321: $i,X4322: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4321 @ X4322 ) ) )
      = X4321 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( k1_mcart_1 @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_mcart_1 @ sk_B_80 )
    = ( k1_mcart_1 @ sk_C_93 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_mcart_1 @ sk_B_80 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('51',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( k1_mcart_1 @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( '#_fresh_sk2' @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf('53',plain,
    ( sk_B_80
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( '#_fresh_sk3' @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['13','17'])).

thf('54',plain,(
    ! [X4321: $i,X4323: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4321 @ X4323 ) ) )
      = X4323 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('55',plain,
    ( ( k2_mcart_1 @ sk_B_80 )
    = ( '#_fresh_sk3' @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( '#_fresh_sk3' @ sk_C_93 )
    = ( k2_mcart_1 @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('57',plain,
    ( ( '#_fresh_sk3' @ sk_C_93 )
    = ( '#_fresh_sk3' @ sk_B_80 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_B_80 @ ( '#_fresh_sk3' @ sk_B_80 ) ) ) ),
    inference(demod,[status(thm)],['41','52','57'])).

thf('59',plain,(
    sk_C_93 = sk_B_80 ),
    inference('sup+',[status(thm)],['18','58'])).

thf('60',plain,(
    sk_B_80 != sk_C_93 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
