%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0865+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8jXc1T188z

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 14.41s
% Output     : Refutation 14.41s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 188 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 (1549 expanded)
%              Number of equality atoms :   32 ( 181 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_D_38_type,type,(
    sk_D_38: $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf('#_fresh_sk3_type',type,(
    '#_fresh_sk3': $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_26_type,type,(
    sk_C_26: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_73_type,type,(
    sk_B_73: $i )).

thf(t23_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ ( A @ B ) )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A @ ( k2_mcart_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ ( A @ B ) )
         => ( A
            = ( k4_tarski @ ( k1_mcart_1 @ A @ ( k2_mcart_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_mcart_1])).

thf('0',plain,(
    sk_A_14
 != ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_14 @ sk_B_73 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ ( B @ A ) )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ ( C @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X2089: $i,X2090: $i] :
      ( ( X2089
        = ( k4_tarski @ ( sk_C_26 @ X2089 @ ( sk_D_38 @ X2089 ) ) ) )
      | ~ ( r2_hidden @ ( X2089 @ X2090 ) )
      | ~ ( v1_relat_1 @ X2090 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B_73 )
    | ( sk_A_14
      = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_73 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_C_26 @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ ( A @ B ) )
        = ( k4_tarski @ ( C @ D ) ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('7',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1285 = X1284 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('8',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1285 ) ),
    inference(inj_rec,[status(thm)],['7'])).

thf('9',plain,
    ( ( '#_fresh_sk2' @ sk_A_14 )
    = ( sk_C_26 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['5','9'])).

thf('11',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( sk_D_38 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['5','9'])).

thf('12',plain,(
    ! [X1284: $i,X1285: $i,X1286: $i,X1287: $i] :
      ( ( X1287 = X1286 )
      | ( ( k4_tarski @ ( X1285 @ X1287 ) )
       != ( k4_tarski @ ( X1284 @ X1286 ) ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('13',plain,(
    ! [X1285: $i,X1287: $i] :
      ( ( '#_fresh_sk3' @ ( k4_tarski @ ( X1285 @ X1287 ) ) )
      = X1287 ) ),
    inference(inj_rec,[status(thm)],['12'])).

thf('14',plain,
    ( ( '#_fresh_sk3' @ sk_A_14 )
    = ( sk_D_38 @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['10','14'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('16',plain,(
    ! [X3912: $i,X3913: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3912 @ X3913 ) ) )
      = X3912 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = ( '#_fresh_sk2' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A_14
 != ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['10','14'])).

thf('20',plain,(
    ! [X3912: $i,X3914: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3912 @ X3914 ) ) )
      = X3914 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = ( '#_fresh_sk3' @ sk_A_14 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A_14
    = ( k4_tarski @ ( '#_fresh_sk2' @ sk_A_14 @ ( '#_fresh_sk3' @ sk_A_14 ) ) ) ),
    inference(demod,[status(thm)],['10','14'])).

thf('23',plain,(
    sk_A_14 != sk_A_14 ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
