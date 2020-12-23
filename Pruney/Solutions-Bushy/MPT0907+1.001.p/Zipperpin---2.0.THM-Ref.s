%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0907+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F1telZBsIq

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  268 ( 495 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t66_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
      | ( X2
       != ( k1_mcart_1 @ X2 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
      | ( X2
       != ( k1_mcart_1 @ X2 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X4 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( sk_A
     != ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('13',plain,(
    m1_subset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
      | ( X2
       != ( k2_mcart_1 @ X2 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_mcart_1])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k2_zfmisc_1 @ X3 @ X4 ) )
      | ( X2
       != ( k2_mcart_1 @ X2 ) )
      | ( ( k2_zfmisc_1 @ X3 @ X4 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( sk_A
     != ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
        = o_0_0_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('23',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('25',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['11','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['9','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_C )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['2','28','29'])).


%------------------------------------------------------------------------------
