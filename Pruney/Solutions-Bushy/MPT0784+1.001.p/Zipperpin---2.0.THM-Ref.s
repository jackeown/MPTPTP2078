%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1Q2uiquMXV

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:29 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 222 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :   30
%              Number of atoms          : 1445 (2989 expanded)
%              Number of equality atoms :  118 ( 192 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t33_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( v2_wellord1 @ C )
       => ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( v2_wellord1 @ C )
         => ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_wellord1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( r2_hidden @ X26 @ ( k3_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord1])).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_wellord1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ( r2_hidden @ X26 @ ( k3_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord1])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v6_relat_2 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X21 )
      | ( X22 = X23 )
      | ~ ( r2_hidden @ X23 @ ( k3_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ~ ( v6_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X1 = X2 )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X0 ) )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v6_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X0 )
      | ( X2 = X1 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( X1 = X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( X2 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X1 = X2 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v8_relat_2 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X1 )
      | ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_wellord1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X2 ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) ) @ X1 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) ) @ X1 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X2 ) @ X3 )
      | ( r2_hidden @ X1 @ ( k1_wellord1 @ X0 @ X2 ) )
      | ~ ( v6_relat_2 @ X0 )
      | ( X2 = X1 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X1 )
      | ~ ( v6_relat_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_wellord1 @ X0 @ X2 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X2 ) @ X3 )
      | ~ ( v8_relat_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ( ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) )
        = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_wellord1 @ X0 @ X2 ) ) @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v8_relat_2 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X2 ) @ X3 )
      | ( r2_hidden @ X1 @ ( k1_wellord1 @ X0 @ X2 ) )
      | ~ ( v6_relat_2 @ X0 )
      | ( X2 = X1 )
      | ( ( k1_wellord1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ~ ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X0 )
      | ~ ( v6_relat_2 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ X1 @ X2 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v8_relat_2 @ X1 )
      | ( ( sk_C @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) )
        = X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) )
        = X0 )
      | ~ ( v8_relat_2 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ X1 @ X2 ) )
      | ~ ( v6_relat_2 @ X1 )
      | ( X2 = X0 )
      | ( ( k1_wellord1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_wellord1 @ X2 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X1 = X0 )
      | ~ ( v6_relat_2 @ X2 )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X2 @ X1 ) @ ( k1_wellord1 @ X2 @ X0 ) )
      | ~ ( v8_relat_2 @ X2 )
      | ( r1_tarski @ ( k1_wellord1 @ X2 @ X1 ) @ ( k1_wellord1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v8_relat_2 @ X2 )
      | ( r1_tarski @ ( k1_wellord1 @ X2 @ X1 ) @ ( k1_wellord1 @ X2 @ X0 ) )
      | ~ ( v6_relat_2 @ X2 )
      | ( X1 = X0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X2 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_wellord1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X0 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ( r3_xboole_0 @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v8_relat_2 @ sk_C_4 )
    | ~ ( v6_relat_2 @ sk_C_4 )
    | ( sk_B_3 = sk_A )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v8_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('36',plain,
    ( ( v8_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v8_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v6_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('41',plain,
    ( ( v6_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v6_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_B_3 = sk_A )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['33','38','43','44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('47',plain,
    ( ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( sk_B_3 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( sk_B_3 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v8_relat_2 @ X2 )
      | ( r1_tarski @ ( k1_wellord1 @ X2 @ X1 ) @ ( k1_wellord1 @ X2 @ X0 ) )
      | ~ ( v6_relat_2 @ X2 )
      | ( X1 = X0 )
      | ( ( k1_wellord1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X2 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X0 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_wellord1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_wellord1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 = X0 )
      | ~ ( v6_relat_2 @ X1 )
      | ~ ( v8_relat_2 @ X1 )
      | ( r3_xboole_0 @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v8_relat_2 @ sk_C_4 )
    | ~ ( v6_relat_2 @ sk_C_4 )
    | ( sk_A = sk_B_3 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v8_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['36','37'])).

thf('56',plain,(
    v6_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['41','42'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_A = sk_B_3 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('60',plain,
    ( ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v4_relat_2 @ X18 )
      | ( X20 = X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('64',plain,
    ( ( sk_A = sk_B_3 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 )
    | ~ ( v4_relat_2 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X10: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ( v4_relat_2 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('68',plain,
    ( ( v4_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = sk_B_3 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 ) ),
    inference(demod,[status(thm)],['64','65','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_B_3 = sk_A )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B_3 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','72'])).

thf('74',plain,
    ( ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_B_3 )
      = k1_xboole_0 )
    | ( sk_B_3 = sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ k1_xboole_0 )
    | ( sk_B_3 = sk_A )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('77',plain,(
    ! [X27: $i] :
      ( r1_tarski @ k1_xboole_0 @ X27 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( r3_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B_3 = sk_A )
    | ( ( k1_wellord1 @ sk_C_4 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( r3_xboole_0 @ k1_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
    | ( sk_B_3 = sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X27: $i] :
      ( r1_tarski @ k1_xboole_0 @ X27 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r3_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( r3_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B_3 = sk_A ),
    inference(demod,[status(thm)],['82','85'])).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ A @ A ) )).

thf('87',plain,(
    ! [X24: $i] :
      ( r3_xboole_0 @ X24 @ X24 ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86','87'])).


%------------------------------------------------------------------------------
