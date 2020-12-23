%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0446+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i2k6BkT9Bv

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 497 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('19',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k2_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['17','28'])).


%------------------------------------------------------------------------------
