%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B7jR43u4HQ

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  190 ( 323 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(a_2_0_mcart_1_type,type,(
    a_2_0_mcart_1: $i > $i > $i )).

thf(t93_mcart_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k11_relat_1 @ A @ ( k1_mcart_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_mcart_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fraenkel_a_2_0_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( v1_relat_1 @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_0_mcart_1 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( ( k1_mcart_1 @ D )
              = C )
            & ( A
              = ( k2_mcart_1 @ D ) )
            & ( m1_subset_1 @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X2 @ ( a_2_0_mcart_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ X0 )
      | ( X2
       != ( k2_mcart_1 @ X3 ) )
      | ( ( k1_mcart_1 @ X3 )
       != X1 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ ( a_2_0_mcart_1 @ X0 @ ( k1_mcart_1 @ X3 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( a_2_0_mcart_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_mcart_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( a_2_0_mcart_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( a_2_0_mcart_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t92_mcart_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k11_relat_1 @ sk_A @ X0 )
        = ( a_2_0_mcart_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_A @ X0 )
      = ( a_2_0_mcart_1 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_B ) @ ( k11_relat_1 @ sk_A @ ( k1_mcart_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).


%------------------------------------------------------------------------------
