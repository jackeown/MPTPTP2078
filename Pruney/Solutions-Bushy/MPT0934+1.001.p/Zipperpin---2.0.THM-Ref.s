%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0934+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.guq3mgSGHZ

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 ( 566 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t95_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
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
            ( ( m1_subset_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( ( ( k1_mcart_1 @ B )
                      = ( k1_mcart_1 @ C ) )
                    & ( ( k2_mcart_1 @ B )
                      = ( k2_mcart_1 @ C ) ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_B )
    = ( k1_mcart_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r2_hidden @ A @ B )
            & ( ( k1_mcart_1 @ C )
              = ( k1_mcart_1 @ A ) )
            & ( ( k2_mcart_1 @ C )
              = ( k2_mcart_1 @ A ) ) )
         => ( C = A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( ( k1_mcart_1 @ X2 )
       != ( k1_mcart_1 @ X4 ) )
      | ( ( k2_mcart_1 @ X2 )
       != ( k2_mcart_1 @ X4 ) )
      | ( X2 = X4 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_B )
       != ( k1_mcart_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( sk_C = X0 )
      | ( ( k2_mcart_1 @ sk_C )
       != ( k2_mcart_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_mcart_1 @ sk_B )
    = ( k2_mcart_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_B )
       != ( k1_mcart_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( sk_C = X0 )
      | ( ( k2_mcart_1 @ sk_B )
       != ( k2_mcart_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_C @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_C @ X0 )
      | ( ( k2_mcart_1 @ sk_B )
       != ( k2_mcart_1 @ sk_B ) )
      | ( sk_C = sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( sk_C = sk_B )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['14','19','20'])).


%------------------------------------------------------------------------------
