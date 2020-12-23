%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0933+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U9E77Pm3f8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 13.65s
% Output     : Refutation 13.65s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 361 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  401 (3960 expanded)
%              Number of equality atoms :   63 ( 557 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_26_type,type,(
    sk_C_26: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_38_type,type,(
    sk_D_38: $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_B_80_type,type,(
    sk_B_80: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(t94_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( ( r2_hidden @ ( C @ B ) )
            & ( r2_hidden @ ( A @ B ) )
            & ( ( k1_mcart_1 @ C )
              = ( k1_mcart_1 @ A ) )
            & ( ( k2_mcart_1 @ C )
              = ( k2_mcart_1 @ A ) ) )
         => ( C = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( A @ B ) )
              & ( ( k1_mcart_1 @ C )
                = ( k1_mcart_1 @ A ) )
              & ( ( k2_mcart_1 @ C )
                = ( k2_mcart_1 @ A ) ) )
           => ( C = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_mcart_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_14 @ sk_B_80 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ ( B @ A ) )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ ( C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X2089: $i,X2090: $i] :
      ( ( X2089
        = ( k4_tarski @ ( sk_C_26 @ X2089 @ ( sk_D_38 @ X2089 ) ) ) )
      | ~ ( r2_hidden @ ( X2089 @ X2090 ) )
      | ~ ( v1_relat_1 @ X2090 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B_80 )
    | ( sk_A_14
      = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_80 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ ( A @ B ) )
        = ( k4_tarski @ ( C @ D ) ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('6',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1285 = X1284 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('7',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['6'])).

thf('8',plain,
    ( ( '#_fresh_sk1' @ sk_A_14 )
    = ( sk_C_26 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['4','8'])).

thf('10',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['4','8'])).

thf('11',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1287 = X1286 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('12',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('13',plain,
    ( ( '#_fresh_sk2' @ sk_A_14 )
    = ( sk_D_38 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( '#_fresh_sk2' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_C_93 @ sk_B_80 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2089: $i,X2090: $i] :
      ( ( X2089
        = ( k4_tarski @ ( sk_C_26 @ X2089 @ ( sk_D_38 @ X2089 ) ) ) )
      | ~ ( r2_hidden @ ( X2089 @ X2090 ) )
      | ~ ( v1_relat_1 @ X2090 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_B_80 )
    | ( sk_C_93
      = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B_80 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('21',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['6'])).

thf('22',plain,
    ( ( '#_fresh_sk1' @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X4321: $i,X4323: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4321 @ X4323 ) ) )
      = X4323 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k2_mcart_1 @ sk_C_93 )
    = ( sk_D_38 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_mcart_1 @ sk_C_93 )
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( sk_D_38 @ sk_C_93 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_C_93 @ ( k2_mcart_1 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_C_93 @ ( k2_mcart_1 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('31',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('32',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_C_93 @ ( '#_fresh_sk2' @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( '#_fresh_sk2' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('35',plain,(
    ! [X4321: $i,X4322: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4321 @ X4322 ) ) )
      = X4321 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('36',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( '#_fresh_sk1' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_C_93
    = ( k4_tarski @ ( sk_C_26 @ sk_C_93 @ ( sk_D_38 @ sk_C_93 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    ! [X4321: $i,X4322: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4321 @ X4322 ) ) )
      = X4321 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('39',plain,
    ( ( k1_mcart_1 @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_mcart_1 @ sk_C_93 )
    = ( k1_mcart_1 @ sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( '#_fresh_sk1' @ sk_C_93 )
    = ( sk_C_26 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('43',plain,
    ( ( '#_fresh_sk1' @ sk_C_93 )
    = ( k1_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( '#_fresh_sk1' @ sk_C_93 )
    = ( '#_fresh_sk1' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( '#_fresh_sk2' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('46',plain,(
    ! [X4321: $i,X4323: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4321 @ X4323 ) ) )
      = X4323 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( '#_fresh_sk2' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( k2_mcart_1 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('49',plain,
    ( ( '#_fresh_sk2' @ sk_C_93 )
    = ( '#_fresh_sk2' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_C_93
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A_14 @ ( '#_fresh_sk2' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['33','44','49'])).

thf('51',plain,(
    sk_C_93 = sk_A_14 ),
    inference('sup+',[status(thm)],['14','50'])).

thf('52',plain,(
    sk_C_93 != sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
