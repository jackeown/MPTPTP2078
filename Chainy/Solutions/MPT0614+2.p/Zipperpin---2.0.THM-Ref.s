%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0614+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IT0bnvmDLQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 9.82s
% Output     : Refutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  150 ( 247 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_6_type,type,(
    sk_A_6: $i )).

thf(sk_C_35_type,type,(
    sk_C_35: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t218_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ ( C @ A ) ) )
         => ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v5_relat_1 @ ( C @ A ) ) )
           => ( v5_relat_1 @ ( C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t218_relat_1])).

thf('0',plain,(
    ~ ( v5_relat_1 @ ( sk_C_35 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ ( sk_C_35 @ sk_A_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_C_35 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_35 @ sk_A_6 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_35 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_35 @ sk_A_6 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( sk_A_6 @ sk_B_15 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) )
    = sk_A_6 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('10',plain,(
    ! [X177: $i,X178: $i,X179: $i] :
      ( ( r1_tarski @ ( X177 @ X178 ) )
      | ~ ( r1_tarski @ ( X177 @ ( k3_xboole_0 @ ( X178 @ X179 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_6 ) )
      | ( r1_tarski @ ( X0 @ sk_B_15 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_35 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C_35 )
    | ( v5_relat_1 @ ( sk_C_35 @ sk_B_15 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_35 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_relat_1 @ ( sk_C_35 @ sk_B_15 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
