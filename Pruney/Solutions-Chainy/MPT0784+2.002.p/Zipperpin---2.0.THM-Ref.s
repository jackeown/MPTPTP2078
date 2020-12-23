%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2JE0tyVUo0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:32 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 348 expanded)
%              Number of leaves         :   27 ( 107 expanded)
%              Depth                    :   39
%              Number of atoms          : 1291 (3889 expanded)
%              Number of equality atoms :   58 ( 130 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k1_wellord1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('3',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_wellord1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r3_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X2 ) )
      | ( r3_xboole_0 @ X0 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_4 ) )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_B_3 @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r3_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X2 ) )
      | ( r3_xboole_0 @ ( k1_wellord1 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v6_relat_2 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( k3_relat_1 @ X25 ) )
      | ( r2_hidden @ ( k4_tarski @ X27 @ X26 ) @ X25 )
      | ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ X25 )
      | ( X26 = X27 )
      | ~ ( r2_hidden @ X27 @ ( k3_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_4 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 )
      | ~ ( v6_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X17: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ( v6_relat_2 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('26',plain,
    ( ( v6_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v6_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_4 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_4 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X14
       != ( k1_wellord1 @ X13 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X12 ) @ X13 )
      | ( X16 = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( X16 = X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X12 ) @ X13 )
      | ( r2_hidden @ X16 @ ( k1_wellord1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_3 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_B_3 = sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ! [B: $i,C: $i,D: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v8_relat_2 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l2_wellord1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ~ ( v8_relat_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ sk_B_3 ) @ sk_C_4 )
      | ~ ( v8_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ( v8_relat_2 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('45',plain,
    ( ( v8_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v8_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_3 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ sk_B_3 ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['41','42','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( X16 = X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X12 ) @ X13 )
      | ( r2_hidden @ X16 @ ( k1_wellord1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ( sk_A = sk_B_3 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
        = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ( sk_A = sk_B_3 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
        = sk_B_3 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      = sk_B_3 )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_A = sk_B_3 )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      = sk_B_3 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r3_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('60',plain,
    ( ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_A = sk_B_3 )
    | ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ sk_B_3 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_wellord1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X12 ) @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('64',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 )
    | ~ ( v1_relat_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v8_relat_2 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X0 @ X1 ) ) @ X3 ) @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_3 )
      | ~ ( v1_relat_1 @ sk_C_4 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) @ sk_A ) @ sk_C_4 )
      | ~ ( v8_relat_2 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v8_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['45','46'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B_3 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) @ sk_A ) @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( X16 = X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X12 ) @ X13 )
      | ( r2_hidden @ X16 @ ( k1_wellord1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ X0 )
      | ( sk_A = sk_B_3 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ X0 )
      | ( sk_A = sk_B_3 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
      = sk_A )
    | ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_A = sk_B_3 )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('80',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) )
    | ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_A = sk_B_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_3 @ sk_A ) @ sk_C_4 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(l3_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v4_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) )
           => ( B = C ) ) ) ) )).

thf('85',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v4_relat_2 @ X22 )
      | ( X24 = X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X23 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l3_wellord1])).

thf('86',plain,
    ( ( sk_A = sk_B_3 )
    | ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 )
    | ~ ( v4_relat_2 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X17: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ( v4_relat_2 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('90',plain,
    ( ( v4_relat_2 @ sk_C_4 )
    | ~ ( v2_wellord1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_wellord1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_relat_2 @ sk_C_4 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A = sk_B_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 ) ),
    inference(demod,[status(thm)],['86','87','92'])).

thf('94',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_3 ) @ sk_C_4 )
    | ( sk_A = sk_B_3 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( sk_A = sk_B_3 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) @ ( k1_wellord1 @ sk_C_4 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r3_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('97',plain,
    ( ( sk_A = sk_B_3 )
    | ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( r3_xboole_0 @ ( k1_wellord1 @ sk_C_4 @ sk_A ) @ ( k1_wellord1 @ sk_C_4 @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_A = sk_B_3 ),
    inference(clc,[status(thm)],['97','98'])).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ A @ A ) )).

thf('100',plain,(
    ! [X7: $i] :
      ( r3_xboole_0 @ X7 @ X7 ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2JE0tyVUo0
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.27/1.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.48  % Solved by: fo/fo7.sh
% 1.27/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.48  % done 903 iterations in 1.016s
% 1.27/1.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.48  % SZS output start Refutation
% 1.27/1.48  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 1.27/1.48  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.27/1.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.27/1.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.27/1.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.27/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.48  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 1.27/1.48  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 1.27/1.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.27/1.48  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 1.27/1.48  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 1.27/1.48  thf(sk_C_4_type, type, sk_C_4: $i).
% 1.27/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.48  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 1.27/1.48  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 1.27/1.48  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 1.27/1.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.27/1.48  thf(t33_wellord1, conjecture,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ C ) =>
% 1.27/1.48       ( ( v2_wellord1 @ C ) =>
% 1.27/1.48         ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ))).
% 1.27/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.48    (~( ![A:$i,B:$i,C:$i]:
% 1.27/1.48        ( ( v1_relat_1 @ C ) =>
% 1.27/1.48          ( ( v2_wellord1 @ C ) =>
% 1.27/1.48            ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) )),
% 1.27/1.48    inference('cnf.neg', [status(esa)], [t33_wellord1])).
% 1.27/1.48  thf('0', plain,
% 1.27/1.48      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(d3_tarski, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( r1_tarski @ A @ B ) <=>
% 1.27/1.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.27/1.48  thf('1', plain,
% 1.27/1.48      (![X1 : $i, X3 : $i]:
% 1.27/1.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.27/1.48  thf(d1_wellord1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ![B:$i,C:$i]:
% 1.27/1.48         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 1.27/1.48           ( ![D:$i]:
% 1.27/1.48             ( ( r2_hidden @ D @ C ) <=>
% 1.27/1.48               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 1.27/1.48  thf('2', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.27/1.48         (((X14) != (k1_wellord1 @ X13 @ X12))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X15 @ X12) @ X13)
% 1.27/1.48          | ~ (r2_hidden @ X15 @ X14)
% 1.27/1.48          | ~ (v1_relat_1 @ X13))),
% 1.27/1.48      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.27/1.48  thf('3', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X13)
% 1.27/1.48          | ~ (r2_hidden @ X15 @ (k1_wellord1 @ X13 @ X12))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X15 @ X12) @ X13))),
% 1.27/1.48      inference('simplify', [status(thm)], ['2'])).
% 1.27/1.48  thf('4', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.27/1.48          | ~ (v1_relat_1 @ X1))),
% 1.27/1.48      inference('sup-', [status(thm)], ['1', '3'])).
% 1.27/1.48  thf(t30_relat_1, axiom,
% 1.27/1.48    (![A:$i,B:$i,C:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ C ) =>
% 1.27/1.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.27/1.48         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 1.27/1.48           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 1.27/1.48  thf('5', plain,
% 1.27/1.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.27/1.48         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 1.27/1.48          | (r2_hidden @ X9 @ (k3_relat_1 @ X10))
% 1.27/1.48          | ~ (v1_relat_1 @ X10))),
% 1.27/1.48      inference('cnf', [status(esa)], [t30_relat_1])).
% 1.27/1.48  thf('6', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X0)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0)
% 1.27/1.48          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['4', '5'])).
% 1.27/1.48  thf('7', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0))),
% 1.27/1.48      inference('simplify', [status(thm)], ['6'])).
% 1.27/1.48  thf(d9_xboole_0, axiom,
% 1.27/1.48    (![A:$i,B:$i]:
% 1.27/1.48     ( ( r3_xboole_0 @ A @ B ) <=>
% 1.27/1.48       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 1.27/1.48  thf('8', plain,
% 1.27/1.48      (![X5 : $i, X6 : $i]: ((r3_xboole_0 @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 1.27/1.48      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.27/1.48  thf('9', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X2)
% 1.27/1.48          | (r2_hidden @ X1 @ (k3_relat_1 @ X2))
% 1.27/1.48          | (r3_xboole_0 @ X0 @ (k1_wellord1 @ X2 @ X1)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['7', '8'])).
% 1.27/1.48  thf('10', plain,
% 1.27/1.48      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('11', plain,
% 1.27/1.48      (((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_4)) | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['9', '10'])).
% 1.27/1.48  thf('12', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('13', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['11', '12'])).
% 1.27/1.48  thf('14', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0))),
% 1.27/1.48      inference('simplify', [status(thm)], ['6'])).
% 1.27/1.48  thf('15', plain,
% 1.27/1.48      (![X5 : $i, X6 : $i]: ((r3_xboole_0 @ X5 @ X6) | ~ (r1_tarski @ X5 @ X6))),
% 1.27/1.48      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.27/1.48  thf('16', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X2)
% 1.27/1.48          | (r2_hidden @ X1 @ (k3_relat_1 @ X2))
% 1.27/1.48          | (r3_xboole_0 @ (k1_wellord1 @ X2 @ X1) @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['14', '15'])).
% 1.27/1.48  thf('17', plain,
% 1.27/1.48      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('18', plain,
% 1.27/1.48      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4)) | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['16', '17'])).
% 1.27/1.48  thf('19', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('20', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['18', '19'])).
% 1.27/1.48  thf(l4_wellord1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ( v6_relat_2 @ A ) <=>
% 1.27/1.48         ( ![B:$i,C:$i]:
% 1.27/1.48           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 1.27/1.48                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 1.27/1.48                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 1.27/1.48                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 1.27/1.48  thf('21', plain,
% 1.27/1.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.27/1.48         (~ (v6_relat_2 @ X25)
% 1.27/1.48          | ~ (r2_hidden @ X26 @ (k3_relat_1 @ X25))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X27 @ X26) @ X25)
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X26 @ X27) @ X25)
% 1.27/1.48          | ((X26) = (X27))
% 1.27/1.48          | ~ (r2_hidden @ X27 @ (k3_relat_1 @ X25))
% 1.27/1.48          | ~ (v1_relat_1 @ X25))),
% 1.27/1.48      inference('cnf', [status(esa)], [l4_wellord1])).
% 1.27/1.48  thf('22', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ sk_C_4)
% 1.27/1.48          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 1.27/1.48          | ((sk_A) = (X0))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4)
% 1.27/1.48          | ~ (v6_relat_2 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['20', '21'])).
% 1.27/1.48  thf('23', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('24', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf(d4_wellord1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ( v2_wellord1 @ A ) <=>
% 1.27/1.48         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 1.27/1.48           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 1.27/1.48  thf('25', plain,
% 1.27/1.48      (![X17 : $i]:
% 1.27/1.48         (~ (v2_wellord1 @ X17) | (v6_relat_2 @ X17) | ~ (v1_relat_1 @ X17))),
% 1.27/1.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.27/1.48  thf('26', plain, (((v6_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['24', '25'])).
% 1.27/1.48  thf('27', plain, ((v2_wellord1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('28', plain, ((v6_relat_2 @ sk_C_4)),
% 1.27/1.48      inference('demod', [status(thm)], ['26', '27'])).
% 1.27/1.48  thf('29', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 1.27/1.48          | ((sk_A) = (X0))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['22', '23', '28'])).
% 1.27/1.48  thf('30', plain,
% 1.27/1.48      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4)
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['13', '29'])).
% 1.27/1.48  thf('31', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 1.27/1.48         (((X14) != (k1_wellord1 @ X13 @ X12))
% 1.27/1.48          | (r2_hidden @ X16 @ X14)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X16 @ X12) @ X13)
% 1.27/1.48          | ((X16) = (X12))
% 1.27/1.48          | ~ (v1_relat_1 @ X13))),
% 1.27/1.48      inference('cnf', [status(esa)], [d1_wellord1])).
% 1.27/1.48  thf('32', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X16 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X13)
% 1.27/1.48          | ((X16) = (X12))
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X16 @ X12) @ X13)
% 1.27/1.48          | (r2_hidden @ X16 @ (k1_wellord1 @ X13 @ X12)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['31'])).
% 1.27/1.48  thf('33', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_B_3) = (sk_A))
% 1.27/1.48        | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['30', '32'])).
% 1.27/1.48  thf('34', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('35', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_B_3) = (sk_A)))),
% 1.27/1.48      inference('demod', [status(thm)], ['33', '34'])).
% 1.27/1.48  thf('36', plain,
% 1.27/1.48      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['35'])).
% 1.27/1.48  thf('37', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.27/1.48          | ~ (v1_relat_1 @ X1))),
% 1.27/1.48      inference('sup-', [status(thm)], ['1', '3'])).
% 1.27/1.48  thf(l2_wellord1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ( v8_relat_2 @ A ) <=>
% 1.27/1.48         ( ![B:$i,C:$i,D:$i]:
% 1.27/1.48           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 1.27/1.48               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 1.27/1.48             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 1.27/1.48  thf('38', plain,
% 1.27/1.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.27/1.48         (~ (v8_relat_2 @ X18)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X18)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X18)
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X18)
% 1.27/1.48          | ~ (v1_relat_1 @ X18))),
% 1.27/1.48      inference('cnf', [status(esa)], [l2_wellord1])).
% 1.27/1.48  thf('39', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X0)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 1.27/1.48          | ~ (v8_relat_2 @ X0))),
% 1.27/1.48      inference('sup-', [status(thm)], ['37', '38'])).
% 1.27/1.48  thf('40', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.27/1.48         (~ (v8_relat_2 @ X0)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0))),
% 1.27/1.48      inference('simplify', [status(thm)], ['39'])).
% 1.27/1.48  thf('41', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | ~ (v1_relat_1 @ sk_C_4)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_3) @ 
% 1.27/1.48             sk_C_4)
% 1.27/1.48          | ~ (v8_relat_2 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['36', '40'])).
% 1.27/1.48  thf('42', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('43', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('44', plain,
% 1.27/1.48      (![X17 : $i]:
% 1.27/1.48         (~ (v2_wellord1 @ X17) | (v8_relat_2 @ X17) | ~ (v1_relat_1 @ X17))),
% 1.27/1.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.27/1.48  thf('45', plain, (((v8_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['43', '44'])).
% 1.27/1.48  thf('46', plain, ((v2_wellord1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('47', plain, ((v8_relat_2 @ sk_C_4)),
% 1.27/1.48      inference('demod', [status(thm)], ['45', '46'])).
% 1.27/1.48  thf('48', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_3) @ 
% 1.27/1.48             sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['41', '42', '47'])).
% 1.27/1.48  thf('49', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X16 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X13)
% 1.27/1.48          | ((X16) = (X12))
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X16 @ X12) @ X13)
% 1.27/1.48          | (r2_hidden @ X16 @ (k1_wellord1 @ X13 @ X12)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['31'])).
% 1.27/1.48  thf('50', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 1.27/1.48          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | ((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 1.27/1.48             (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3))
% 1.27/1.48          | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['48', '49'])).
% 1.27/1.48  thf('51', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('52', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 1.27/1.48          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | ((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 1.27/1.48             (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3)))),
% 1.27/1.48      inference('demod', [status(thm)], ['50', '51'])).
% 1.27/1.48  thf('53', plain,
% 1.27/1.48      (![X1 : $i, X3 : $i]:
% 1.27/1.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.27/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.27/1.48  thf('54', plain,
% 1.27/1.48      ((((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['52', '53'])).
% 1.27/1.48  thf('55', plain,
% 1.27/1.48      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48         (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | ((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48            (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['54'])).
% 1.27/1.48  thf('56', plain,
% 1.27/1.48      (![X1 : $i, X3 : $i]:
% 1.27/1.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.27/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.27/1.48  thf('57', plain,
% 1.27/1.48      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 1.27/1.48      inference('sup+', [status(thm)], ['55', '56'])).
% 1.27/1.48  thf('58', plain,
% 1.27/1.48      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48         (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['57'])).
% 1.27/1.48  thf('59', plain,
% 1.27/1.48      (![X5 : $i, X6 : $i]: ((r3_xboole_0 @ X5 @ X6) | ~ (r1_tarski @ X5 @ X6))),
% 1.27/1.48      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.27/1.48  thf('60', plain,
% 1.27/1.48      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['58', '59'])).
% 1.27/1.48  thf('61', plain,
% 1.27/1.48      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('62', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('clc', [status(thm)], ['60', '61'])).
% 1.27/1.48  thf('63', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X13)
% 1.27/1.48          | ~ (r2_hidden @ X15 @ (k1_wellord1 @ X13 @ X12))
% 1.27/1.48          | (r2_hidden @ (k4_tarski @ X15 @ X12) @ X13))),
% 1.27/1.48      inference('simplify', [status(thm)], ['2'])).
% 1.27/1.48  thf('64', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4)
% 1.27/1.48        | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['62', '63'])).
% 1.27/1.48  thf('65', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('66', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['64', '65'])).
% 1.27/1.48  thf('67', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.27/1.48         (~ (v8_relat_2 @ X0)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 1.27/1.48          | ~ (v1_relat_1 @ X0))),
% 1.27/1.48      inference('simplify', [status(thm)], ['39'])).
% 1.27/1.48  thf('68', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (((sk_A) = (sk_B_3))
% 1.27/1.48          | ~ (v1_relat_1 @ sk_C_4)
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ sk_A) @ 
% 1.27/1.48             sk_C_4)
% 1.27/1.48          | ~ (v8_relat_2 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['66', '67'])).
% 1.27/1.48  thf('69', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('70', plain, ((v8_relat_2 @ sk_C_4)),
% 1.27/1.48      inference('demod', [status(thm)], ['45', '46'])).
% 1.27/1.48  thf('71', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         (((sk_A) = (sk_B_3))
% 1.27/1.48          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ sk_A) @ 
% 1.27/1.48             sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.27/1.48  thf('72', plain,
% 1.27/1.48      (![X12 : $i, X13 : $i, X16 : $i]:
% 1.27/1.48         (~ (v1_relat_1 @ X13)
% 1.27/1.48          | ((X16) = (X12))
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X16 @ X12) @ X13)
% 1.27/1.48          | (r2_hidden @ X16 @ (k1_wellord1 @ X13 @ X12)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['31'])).
% 1.27/1.48  thf('73', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 1.27/1.48          | ((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ 
% 1.27/1.48             (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A))
% 1.27/1.48          | ~ (v1_relat_1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['71', '72'])).
% 1.27/1.48  thf('74', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('75', plain,
% 1.27/1.48      (![X0 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 1.27/1.48          | ((sk_A) = (sk_B_3))
% 1.27/1.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ 
% 1.27/1.48             (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A)))),
% 1.27/1.48      inference('demod', [status(thm)], ['73', '74'])).
% 1.27/1.48  thf('76', plain,
% 1.27/1.48      (![X1 : $i, X3 : $i]:
% 1.27/1.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.27/1.48      inference('cnf', [status(esa)], [d3_tarski])).
% 1.27/1.48  thf('77', plain,
% 1.27/1.48      ((((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['75', '76'])).
% 1.27/1.48  thf('78', plain,
% 1.27/1.48      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48         (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | ((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48            (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['77'])).
% 1.27/1.48  thf('79', plain,
% 1.27/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.48         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 1.27/1.48          | (r2_hidden @ 
% 1.27/1.48             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 1.27/1.48          | ~ (v1_relat_1 @ X1))),
% 1.27/1.48      inference('sup-', [status(thm)], ['1', '3'])).
% 1.27/1.48  thf('80', plain,
% 1.27/1.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ~ (v1_relat_1 @ sk_C_4)
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('sup+', [status(thm)], ['78', '79'])).
% 1.27/1.48  thf('81', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('82', plain,
% 1.27/1.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('demod', [status(thm)], ['80', '81'])).
% 1.27/1.48  thf('83', plain,
% 1.27/1.48      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48         (k1_wellord1 @ sk_C_4 @ sk_A))
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4))),
% 1.27/1.48      inference('simplify', [status(thm)], ['82'])).
% 1.27/1.48  thf('84', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4))),
% 1.27/1.48      inference('demod', [status(thm)], ['64', '65'])).
% 1.27/1.48  thf(l3_wellord1, axiom,
% 1.27/1.48    (![A:$i]:
% 1.27/1.48     ( ( v1_relat_1 @ A ) =>
% 1.27/1.48       ( ( v4_relat_2 @ A ) <=>
% 1.27/1.48         ( ![B:$i,C:$i]:
% 1.27/1.48           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 1.27/1.48               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 1.27/1.48             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.27/1.48  thf('85', plain,
% 1.27/1.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.27/1.48         (~ (v4_relat_2 @ X22)
% 1.27/1.48          | ((X24) = (X23))
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X22)
% 1.27/1.48          | ~ (r2_hidden @ (k4_tarski @ X24 @ X23) @ X22)
% 1.27/1.48          | ~ (v1_relat_1 @ X22))),
% 1.27/1.48      inference('cnf', [status(esa)], [l3_wellord1])).
% 1.27/1.48  thf('86', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | ~ (v1_relat_1 @ sk_C_4)
% 1.27/1.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3))
% 1.27/1.48        | ~ (v4_relat_2 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.48  thf('87', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('88', plain, ((v1_relat_1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('89', plain,
% 1.27/1.48      (![X17 : $i]:
% 1.27/1.48         (~ (v2_wellord1 @ X17) | (v4_relat_2 @ X17) | ~ (v1_relat_1 @ X17))),
% 1.27/1.48      inference('cnf', [status(esa)], [d4_wellord1])).
% 1.27/1.48  thf('90', plain, (((v4_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 1.27/1.48      inference('sup-', [status(thm)], ['88', '89'])).
% 1.27/1.48  thf('91', plain, ((v2_wellord1 @ sk_C_4)),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('92', plain, ((v4_relat_2 @ sk_C_4)),
% 1.27/1.48      inference('demod', [status(thm)], ['90', '91'])).
% 1.27/1.48  thf('93', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3)))),
% 1.27/1.48      inference('demod', [status(thm)], ['86', '87', '92'])).
% 1.27/1.48  thf('94', plain,
% 1.27/1.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 1.27/1.48        | ((sk_A) = (sk_B_3)))),
% 1.27/1.48      inference('simplify', [status(thm)], ['93'])).
% 1.27/1.48  thf('95', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 1.27/1.48      inference('clc', [status(thm)], ['83', '94'])).
% 1.27/1.48  thf('96', plain,
% 1.27/1.48      (![X5 : $i, X6 : $i]: ((r3_xboole_0 @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 1.27/1.48      inference('cnf', [status(esa)], [d9_xboole_0])).
% 1.27/1.48  thf('97', plain,
% 1.27/1.48      ((((sk_A) = (sk_B_3))
% 1.27/1.48        | (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 1.27/1.48      inference('sup-', [status(thm)], ['95', '96'])).
% 1.27/1.48  thf('98', plain,
% 1.27/1.48      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 1.27/1.48          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 1.27/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.48  thf('99', plain, (((sk_A) = (sk_B_3))),
% 1.27/1.48      inference('clc', [status(thm)], ['97', '98'])).
% 1.27/1.48  thf(reflexivity_r3_xboole_0, axiom, (![A:$i,B:$i]: ( r3_xboole_0 @ A @ A ))).
% 1.27/1.48  thf('100', plain, (![X7 : $i]: (r3_xboole_0 @ X7 @ X7)),
% 1.27/1.48      inference('cnf', [status(esa)], [reflexivity_r3_xboole_0])).
% 1.27/1.48  thf('101', plain, ($false),
% 1.27/1.48      inference('demod', [status(thm)], ['0', '99', '100'])).
% 1.27/1.48  
% 1.27/1.48  % SZS output end Refutation
% 1.27/1.48  
% 1.27/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
