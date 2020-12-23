%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0868+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hhpVTbvfnG

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 107 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  297 (1252 expanded)
%              Number of equality atoms :   61 ( 259 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4
        = ( k4_tarski @ ( k1_mcart_1 @ X4 ) @ ( k2_mcart_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k2_zfmisc_1 @ X3 @ X5 ) )
      | ( X5 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_C
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_mcart_1 @ X0 ) )
      | ( X0
       != ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_tarski @ X1 @ X2 )
     != ( k2_mcart_1 @ ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C )
     != ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('13',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( $false
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( sk_C
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5','6'])).

thf('18',plain,
    ( ( sk_C
      = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_mcart_1 @ X0 ) )
      | ( X0
       != ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_tarski @ X1 @ X2 )
     != ( k1_mcart_1 @ ( k4_tarski @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) )
     != ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_C
      = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['15','27'])).


%------------------------------------------------------------------------------
