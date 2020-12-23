%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BYB5Ibiozj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:31 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 352 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   39
%              Number of atoms          : 1312 (3919 expanded)
%              Number of equality atoms :   60 ( 132 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X14 ) @ X15 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r3_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r3_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v6_relat_2 @ X27 )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ X29 @ X28 ) @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X29 ) @ X27 )
      | ( X28 = X29 )
      | ~ ( r2_hidden @ X29 @ ( k3_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X19: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ( v6_relat_2 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( X16
       != ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X14 ) @ X15 )
      | ( X18 = X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X18 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X14 ) @ X15 )
      | ( r2_hidden @ X18 @ ( k1_wellord1 @ X15 @ X14 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v8_relat_2 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X19: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ( v8_relat_2 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X18 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X14 ) @ X15 )
      | ( r2_hidden @ X18 @ ( k1_wellord1 @ X15 @ X14 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r3_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X14 ) @ X15 ) ) ),
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
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X18 = X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X14 ) @ X15 )
      | ( r2_hidden @ X18 @ ( k1_wellord1 @ X15 @ X14 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v4_relat_2 @ X24 )
      | ( X26 = X25 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X26 ) @ X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X19: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ( v4_relat_2 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r3_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('100',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r3_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( r3_xboole_0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BYB5Ibiozj
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.60/2.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.60/2.82  % Solved by: fo/fo7.sh
% 2.60/2.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.60/2.82  % done 1321 iterations in 2.351s
% 2.60/2.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.60/2.82  % SZS output start Refutation
% 2.60/2.82  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 2.60/2.82  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 2.60/2.82  thf(sk_A_type, type, sk_A: $i).
% 2.60/2.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.60/2.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.60/2.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.60/2.82  thf(sk_C_4_type, type, sk_C_4: $i).
% 2.60/2.82  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 2.60/2.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.60/2.82  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 2.60/2.82  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 2.60/2.82  thf(sk_B_3_type, type, sk_B_3: $i).
% 2.60/2.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.60/2.82  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 2.60/2.82  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 2.60/2.82  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 2.60/2.82  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.60/2.82  thf(t33_wellord1, conjecture,
% 2.60/2.82    (![A:$i,B:$i,C:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ C ) =>
% 2.60/2.82       ( ( v2_wellord1 @ C ) =>
% 2.60/2.82         ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ))).
% 2.60/2.82  thf(zf_stmt_0, negated_conjecture,
% 2.60/2.82    (~( ![A:$i,B:$i,C:$i]:
% 2.60/2.82        ( ( v1_relat_1 @ C ) =>
% 2.60/2.82          ( ( v2_wellord1 @ C ) =>
% 2.60/2.82            ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) )),
% 2.60/2.82    inference('cnf.neg', [status(esa)], [t33_wellord1])).
% 2.60/2.82  thf('0', plain,
% 2.60/2.82      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf(d3_tarski, axiom,
% 2.60/2.82    (![A:$i,B:$i]:
% 2.60/2.82     ( ( r1_tarski @ A @ B ) <=>
% 2.60/2.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.60/2.82  thf('1', plain,
% 2.60/2.82      (![X1 : $i, X3 : $i]:
% 2.60/2.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.60/2.82      inference('cnf', [status(esa)], [d3_tarski])).
% 2.60/2.82  thf(d1_wellord1, axiom,
% 2.60/2.82    (![A:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ A ) =>
% 2.60/2.82       ( ![B:$i,C:$i]:
% 2.60/2.82         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 2.60/2.82           ( ![D:$i]:
% 2.60/2.82             ( ( r2_hidden @ D @ C ) <=>
% 2.60/2.82               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 2.60/2.82  thf('2', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.60/2.82         (((X16) != (k1_wellord1 @ X15 @ X14))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X17 @ X14) @ X15)
% 2.60/2.82          | ~ (r2_hidden @ X17 @ X16)
% 2.60/2.82          | ~ (v1_relat_1 @ X15))),
% 2.60/2.82      inference('cnf', [status(esa)], [d1_wellord1])).
% 2.60/2.82  thf('3', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X17 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X15)
% 2.60/2.82          | ~ (r2_hidden @ X17 @ (k1_wellord1 @ X15 @ X14))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X17 @ X14) @ X15))),
% 2.60/2.82      inference('simplify', [status(thm)], ['2'])).
% 2.60/2.82  thf('4', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 2.60/2.82          | ~ (v1_relat_1 @ X1))),
% 2.60/2.82      inference('sup-', [status(thm)], ['1', '3'])).
% 2.60/2.82  thf(t30_relat_1, axiom,
% 2.60/2.82    (![A:$i,B:$i,C:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ C ) =>
% 2.60/2.82       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 2.60/2.82         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 2.60/2.82           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 2.60/2.82  thf('5', plain,
% 2.60/2.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.60/2.82         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 2.60/2.82          | (r2_hidden @ X11 @ (k3_relat_1 @ X12))
% 2.60/2.82          | ~ (v1_relat_1 @ X12))),
% 2.60/2.82      inference('cnf', [status(esa)], [t30_relat_1])).
% 2.60/2.82  thf('6', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X0)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0)
% 2.60/2.82          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['4', '5'])).
% 2.60/2.82  thf('7', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0))),
% 2.60/2.82      inference('simplify', [status(thm)], ['6'])).
% 2.60/2.82  thf(d9_xboole_0, axiom,
% 2.60/2.82    (![A:$i,B:$i]:
% 2.60/2.82     ( ( r3_xboole_0 @ A @ B ) <=>
% 2.60/2.82       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 2.60/2.82  thf('8', plain,
% 2.60/2.82      (![X8 : $i, X9 : $i]: ((r3_xboole_0 @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 2.60/2.82      inference('cnf', [status(esa)], [d9_xboole_0])).
% 2.60/2.82  thf('9', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X2)
% 2.60/2.82          | (r2_hidden @ X1 @ (k3_relat_1 @ X2))
% 2.60/2.82          | (r3_xboole_0 @ X0 @ (k1_wellord1 @ X2 @ X1)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['7', '8'])).
% 2.60/2.82  thf('10', plain,
% 2.60/2.82      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('11', plain,
% 2.60/2.82      (((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_4)) | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['9', '10'])).
% 2.60/2.82  thf('12', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('13', plain, ((r2_hidden @ sk_B_3 @ (k3_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['11', '12'])).
% 2.60/2.82  thf('14', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0))),
% 2.60/2.82      inference('simplify', [status(thm)], ['6'])).
% 2.60/2.82  thf('15', plain,
% 2.60/2.82      (![X8 : $i, X9 : $i]: ((r3_xboole_0 @ X8 @ X9) | ~ (r1_tarski @ X8 @ X9))),
% 2.60/2.82      inference('cnf', [status(esa)], [d9_xboole_0])).
% 2.60/2.82  thf('16', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X2)
% 2.60/2.82          | (r2_hidden @ X1 @ (k3_relat_1 @ X2))
% 2.60/2.82          | (r3_xboole_0 @ (k1_wellord1 @ X2 @ X1) @ X0))),
% 2.60/2.82      inference('sup-', [status(thm)], ['14', '15'])).
% 2.60/2.82  thf('17', plain,
% 2.60/2.82      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('18', plain,
% 2.60/2.82      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4)) | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['16', '17'])).
% 2.60/2.82  thf('19', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('20', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['18', '19'])).
% 2.60/2.82  thf(l4_wellord1, axiom,
% 2.60/2.82    (![A:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ A ) =>
% 2.60/2.82       ( ( v6_relat_2 @ A ) <=>
% 2.60/2.82         ( ![B:$i,C:$i]:
% 2.60/2.82           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 2.60/2.82                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 2.60/2.82                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 2.60/2.82                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 2.60/2.82  thf('21', plain,
% 2.60/2.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.60/2.82         (~ (v6_relat_2 @ X27)
% 2.60/2.82          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X27))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X29 @ X28) @ X27)
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X28 @ X29) @ X27)
% 2.60/2.82          | ((X28) = (X29))
% 2.60/2.82          | ~ (r2_hidden @ X29 @ (k3_relat_1 @ X27))
% 2.60/2.82          | ~ (v1_relat_1 @ X27))),
% 2.60/2.82      inference('cnf', [status(esa)], [l4_wellord1])).
% 2.60/2.82  thf('22', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ sk_C_4)
% 2.60/2.82          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 2.60/2.82          | ((sk_A) = (X0))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4)
% 2.60/2.82          | ~ (v6_relat_2 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['20', '21'])).
% 2.60/2.82  thf('23', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('24', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf(d4_wellord1, axiom,
% 2.60/2.82    (![A:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ A ) =>
% 2.60/2.82       ( ( v2_wellord1 @ A ) <=>
% 2.60/2.82         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 2.60/2.82           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 2.60/2.82  thf('25', plain,
% 2.60/2.82      (![X19 : $i]:
% 2.60/2.82         (~ (v2_wellord1 @ X19) | (v6_relat_2 @ X19) | ~ (v1_relat_1 @ X19))),
% 2.60/2.82      inference('cnf', [status(esa)], [d4_wellord1])).
% 2.60/2.82  thf('26', plain, (((v6_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['24', '25'])).
% 2.60/2.82  thf('27', plain, ((v2_wellord1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('28', plain, ((v6_relat_2 @ sk_C_4)),
% 2.60/2.82      inference('demod', [status(thm)], ['26', '27'])).
% 2.60/2.82  thf('29', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_4))
% 2.60/2.82          | ((sk_A) = (X0))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_4)
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['22', '23', '28'])).
% 2.60/2.82  thf('30', plain,
% 2.60/2.82      (((r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4)
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['13', '29'])).
% 2.60/2.82  thf('31', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 2.60/2.82         (((X16) != (k1_wellord1 @ X15 @ X14))
% 2.60/2.82          | (r2_hidden @ X18 @ X16)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X18 @ X14) @ X15)
% 2.60/2.82          | ((X18) = (X14))
% 2.60/2.82          | ~ (v1_relat_1 @ X15))),
% 2.60/2.82      inference('cnf', [status(esa)], [d1_wellord1])).
% 2.60/2.82  thf('32', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X18 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X15)
% 2.60/2.82          | ((X18) = (X14))
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X18 @ X14) @ X15)
% 2.60/2.82          | (r2_hidden @ X18 @ (k1_wellord1 @ X15 @ X14)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['31'])).
% 2.60/2.82  thf('33', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_B_3) = (sk_A))
% 2.60/2.82        | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['30', '32'])).
% 2.60/2.82  thf('34', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('35', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_B_3) = (sk_A)))),
% 2.60/2.82      inference('demod', [status(thm)], ['33', '34'])).
% 2.60/2.82  thf('36', plain,
% 2.60/2.82      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['35'])).
% 2.60/2.82  thf('37', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 2.60/2.82          | ~ (v1_relat_1 @ X1))),
% 2.60/2.82      inference('sup-', [status(thm)], ['1', '3'])).
% 2.60/2.82  thf(l2_wellord1, axiom,
% 2.60/2.82    (![A:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ A ) =>
% 2.60/2.82       ( ( v8_relat_2 @ A ) <=>
% 2.60/2.82         ( ![B:$i,C:$i,D:$i]:
% 2.60/2.82           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 2.60/2.82               ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) =>
% 2.60/2.82             ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) ) ) ) ))).
% 2.60/2.82  thf('38', plain,
% 2.60/2.82      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.60/2.82         (~ (v8_relat_2 @ X20)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X20)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X20)
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X21 @ X23) @ X20)
% 2.60/2.82          | ~ (v1_relat_1 @ X20))),
% 2.60/2.82      inference('cnf', [status(esa)], [l2_wellord1])).
% 2.60/2.82  thf('39', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X0)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 2.60/2.82          | ~ (v8_relat_2 @ X0))),
% 2.60/2.82      inference('sup-', [status(thm)], ['37', '38'])).
% 2.60/2.82  thf('40', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.60/2.82         (~ (v8_relat_2 @ X0)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0))),
% 2.60/2.82      inference('simplify', [status(thm)], ['39'])).
% 2.60/2.82  thf('41', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | ~ (v1_relat_1 @ sk_C_4)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_3) @ 
% 2.60/2.82             sk_C_4)
% 2.60/2.82          | ~ (v8_relat_2 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['36', '40'])).
% 2.60/2.82  thf('42', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('43', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('44', plain,
% 2.60/2.82      (![X19 : $i]:
% 2.60/2.82         (~ (v2_wellord1 @ X19) | (v8_relat_2 @ X19) | ~ (v1_relat_1 @ X19))),
% 2.60/2.82      inference('cnf', [status(esa)], [d4_wellord1])).
% 2.60/2.82  thf('45', plain, (((v8_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['43', '44'])).
% 2.60/2.82  thf('46', plain, ((v2_wellord1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('47', plain, ((v8_relat_2 @ sk_C_4)),
% 2.60/2.82      inference('demod', [status(thm)], ['45', '46'])).
% 2.60/2.82  thf('48', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ sk_B_3) @ 
% 2.60/2.82             sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['41', '42', '47'])).
% 2.60/2.82  thf('49', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X18 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X15)
% 2.60/2.82          | ((X18) = (X14))
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X18 @ X14) @ X15)
% 2.60/2.82          | (r2_hidden @ X18 @ (k1_wellord1 @ X15 @ X14)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['31'])).
% 2.60/2.82  thf('50', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 2.60/2.82          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | ((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 2.60/2.82             (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3))
% 2.60/2.82          | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['48', '49'])).
% 2.60/2.82  thf('51', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('52', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ X0)
% 2.60/2.82          | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | ((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) @ 
% 2.60/2.82             (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3)))),
% 2.60/2.82      inference('demod', [status(thm)], ['50', '51'])).
% 2.60/2.82  thf('53', plain,
% 2.60/2.82      (![X1 : $i, X3 : $i]:
% 2.60/2.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.60/2.82      inference('cnf', [status(esa)], [d3_tarski])).
% 2.60/2.82  thf('54', plain,
% 2.60/2.82      ((((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['52', '53'])).
% 2.60/2.82  thf('55', plain,
% 2.60/2.82      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82         (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | ((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82            (k1_wellord1 @ sk_C_4 @ sk_A)) = (sk_B_3)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['54'])).
% 2.60/2.82  thf('56', plain,
% 2.60/2.82      (![X1 : $i, X3 : $i]:
% 2.60/2.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.60/2.82      inference('cnf', [status(esa)], [d3_tarski])).
% 2.60/2.82  thf('57', plain,
% 2.60/2.82      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 2.60/2.82      inference('sup+', [status(thm)], ['55', '56'])).
% 2.60/2.82  thf('58', plain,
% 2.60/2.82      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82         (k1_wellord1 @ sk_C_4 @ sk_B_3))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['57'])).
% 2.60/2.82  thf('59', plain,
% 2.60/2.82      (![X8 : $i, X9 : $i]: ((r3_xboole_0 @ X8 @ X9) | ~ (r1_tarski @ X8 @ X9))),
% 2.60/2.82      inference('cnf', [status(esa)], [d9_xboole_0])).
% 2.60/2.82  thf('60', plain,
% 2.60/2.82      (((r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['58', '59'])).
% 2.60/2.82  thf('61', plain,
% 2.60/2.82      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('62', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ sk_B_3 @ (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('clc', [status(thm)], ['60', '61'])).
% 2.60/2.82  thf('63', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X17 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X15)
% 2.60/2.82          | ~ (r2_hidden @ X17 @ (k1_wellord1 @ X15 @ X14))
% 2.60/2.82          | (r2_hidden @ (k4_tarski @ X17 @ X14) @ X15))),
% 2.60/2.82      inference('simplify', [status(thm)], ['2'])).
% 2.60/2.82  thf('64', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4)
% 2.60/2.82        | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['62', '63'])).
% 2.60/2.82  thf('65', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('66', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['64', '65'])).
% 2.60/2.82  thf('67', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.60/2.82         (~ (v8_relat_2 @ X0)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X0 @ X1)) @ X3) @ X0)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 2.60/2.82          | ~ (v1_relat_1 @ X0))),
% 2.60/2.82      inference('simplify', [status(thm)], ['39'])).
% 2.60/2.82  thf('68', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (((sk_A) = (sk_B_3))
% 2.60/2.82          | ~ (v1_relat_1 @ sk_C_4)
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ sk_A) @ 
% 2.60/2.82             sk_C_4)
% 2.60/2.82          | ~ (v8_relat_2 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['66', '67'])).
% 2.60/2.82  thf('69', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('70', plain, ((v8_relat_2 @ sk_C_4)),
% 2.60/2.82      inference('demod', [status(thm)], ['45', '46'])).
% 2.60/2.82  thf('71', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         (((sk_A) = (sk_B_3))
% 2.60/2.82          | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ sk_A) @ 
% 2.60/2.82             sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['68', '69', '70'])).
% 2.60/2.82  thf('72', plain,
% 2.60/2.82      (![X14 : $i, X15 : $i, X18 : $i]:
% 2.60/2.82         (~ (v1_relat_1 @ X15)
% 2.60/2.82          | ((X18) = (X14))
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X18 @ X14) @ X15)
% 2.60/2.82          | (r2_hidden @ X18 @ (k1_wellord1 @ X15 @ X14)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['31'])).
% 2.60/2.82  thf('73', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 2.60/2.82          | ((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ 
% 2.60/2.82             (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A))
% 2.60/2.82          | ~ (v1_relat_1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['71', '72'])).
% 2.60/2.82  thf('74', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('75', plain,
% 2.60/2.82      (![X0 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ X0)
% 2.60/2.82          | ((sk_A) = (sk_B_3))
% 2.60/2.82          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) @ 
% 2.60/2.82             (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A)))),
% 2.60/2.82      inference('demod', [status(thm)], ['73', '74'])).
% 2.60/2.82  thf('76', plain,
% 2.60/2.82      (![X1 : $i, X3 : $i]:
% 2.60/2.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.60/2.82      inference('cnf', [status(esa)], [d3_tarski])).
% 2.60/2.82  thf('77', plain,
% 2.60/2.82      ((((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['75', '76'])).
% 2.60/2.82  thf('78', plain,
% 2.60/2.82      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82         (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | ((sk_C @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82            (k1_wellord1 @ sk_C_4 @ sk_B_3)) = (sk_A)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['77'])).
% 2.60/2.82  thf('79', plain,
% 2.60/2.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.82         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 2.60/2.82          | (r2_hidden @ 
% 2.60/2.82             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 2.60/2.82          | ~ (v1_relat_1 @ X1))),
% 2.60/2.82      inference('sup-', [status(thm)], ['1', '3'])).
% 2.60/2.82  thf('80', plain,
% 2.60/2.82      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ~ (v1_relat_1 @ sk_C_4)
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('sup+', [status(thm)], ['78', '79'])).
% 2.60/2.82  thf('81', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('82', plain,
% 2.60/2.82      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('demod', [status(thm)], ['80', '81'])).
% 2.60/2.82  thf('83', plain,
% 2.60/2.82      (((r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82         (k1_wellord1 @ sk_C_4 @ sk_A))
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4))),
% 2.60/2.82      inference('simplify', [status(thm)], ['82'])).
% 2.60/2.82  thf('84', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r2_hidden @ (k4_tarski @ sk_B_3 @ sk_A) @ sk_C_4))),
% 2.60/2.82      inference('demod', [status(thm)], ['64', '65'])).
% 2.60/2.82  thf(l3_wellord1, axiom,
% 2.60/2.82    (![A:$i]:
% 2.60/2.82     ( ( v1_relat_1 @ A ) =>
% 2.60/2.82       ( ( v4_relat_2 @ A ) <=>
% 2.60/2.82         ( ![B:$i,C:$i]:
% 2.60/2.82           ( ( ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 2.60/2.82               ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) =>
% 2.60/2.82             ( ( B ) = ( C ) ) ) ) ) ))).
% 2.60/2.82  thf('85', plain,
% 2.60/2.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.60/2.82         (~ (v4_relat_2 @ X24)
% 2.60/2.82          | ((X26) = (X25))
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X25 @ X26) @ X24)
% 2.60/2.82          | ~ (r2_hidden @ (k4_tarski @ X26 @ X25) @ X24)
% 2.60/2.82          | ~ (v1_relat_1 @ X24))),
% 2.60/2.82      inference('cnf', [status(esa)], [l3_wellord1])).
% 2.60/2.82  thf('86', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | ~ (v1_relat_1 @ sk_C_4)
% 2.60/2.82        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3))
% 2.60/2.82        | ~ (v4_relat_2 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['84', '85'])).
% 2.60/2.82  thf('87', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('88', plain, ((v1_relat_1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('89', plain,
% 2.60/2.82      (![X19 : $i]:
% 2.60/2.82         (~ (v2_wellord1 @ X19) | (v4_relat_2 @ X19) | ~ (v1_relat_1 @ X19))),
% 2.60/2.82      inference('cnf', [status(esa)], [d4_wellord1])).
% 2.60/2.82  thf('90', plain, (((v4_relat_2 @ sk_C_4) | ~ (v2_wellord1 @ sk_C_4))),
% 2.60/2.82      inference('sup-', [status(thm)], ['88', '89'])).
% 2.60/2.82  thf('91', plain, ((v2_wellord1 @ sk_C_4)),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('92', plain, ((v4_relat_2 @ sk_C_4)),
% 2.60/2.82      inference('demod', [status(thm)], ['90', '91'])).
% 2.60/2.82  thf('93', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3)))),
% 2.60/2.82      inference('demod', [status(thm)], ['86', '87', '92'])).
% 2.60/2.82  thf('94', plain,
% 2.60/2.82      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B_3) @ sk_C_4)
% 2.60/2.82        | ((sk_A) = (sk_B_3)))),
% 2.60/2.82      inference('simplify', [status(thm)], ['93'])).
% 2.60/2.82  thf('95', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r1_tarski @ (k1_wellord1 @ sk_C_4 @ sk_B_3) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_A)))),
% 2.60/2.82      inference('clc', [status(thm)], ['83', '94'])).
% 2.60/2.82  thf('96', plain,
% 2.60/2.82      (![X8 : $i, X9 : $i]: ((r3_xboole_0 @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 2.60/2.82      inference('cnf', [status(esa)], [d9_xboole_0])).
% 2.60/2.82  thf('97', plain,
% 2.60/2.82      ((((sk_A) = (sk_B_3))
% 2.60/2.82        | (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82           (k1_wellord1 @ sk_C_4 @ sk_B_3)))),
% 2.60/2.82      inference('sup-', [status(thm)], ['95', '96'])).
% 2.60/2.82  thf('98', plain,
% 2.60/2.82      (~ (r3_xboole_0 @ (k1_wellord1 @ sk_C_4 @ sk_A) @ 
% 2.60/2.82          (k1_wellord1 @ sk_C_4 @ sk_B_3))),
% 2.60/2.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.82  thf('99', plain, (((sk_A) = (sk_B_3))),
% 2.60/2.82      inference('clc', [status(thm)], ['97', '98'])).
% 2.60/2.82  thf(d10_xboole_0, axiom,
% 2.60/2.82    (![A:$i,B:$i]:
% 2.60/2.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.60/2.82  thf('100', plain,
% 2.60/2.82      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.60/2.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.82  thf('101', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.60/2.82      inference('simplify', [status(thm)], ['100'])).
% 2.60/2.82  thf('102', plain,
% 2.60/2.82      (![X8 : $i, X9 : $i]: ((r3_xboole_0 @ X8 @ X9) | ~ (r1_tarski @ X8 @ X9))),
% 2.60/2.82      inference('cnf', [status(esa)], [d9_xboole_0])).
% 2.60/2.82  thf('103', plain, (![X0 : $i]: (r3_xboole_0 @ X0 @ X0)),
% 2.60/2.82      inference('sup-', [status(thm)], ['101', '102'])).
% 2.60/2.82  thf('104', plain, ($false),
% 2.60/2.82      inference('demod', [status(thm)], ['0', '99', '103'])).
% 2.60/2.82  
% 2.60/2.82  % SZS output end Refutation
% 2.60/2.82  
% 2.60/2.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
