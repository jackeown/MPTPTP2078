%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mksDjJdEeG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 784 expanded)
%              Number of leaves         :   29 ( 228 expanded)
%              Depth                    :   37
%              Number of atoms          : 1495 (13011 expanded)
%              Number of equality atoms :   36 ( 526 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X23 @ ( k1_wellord1 @ X23 @ X24 ) ) )
        = ( k1_wellord1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X23 @ ( k1_wellord1 @ X23 @ X24 ) ) )
        = ( k1_wellord1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf(t58_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ~ ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
          & ( A != B )
          & ( r4_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ~ ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
            & ( A != B )
            & ( r4_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_wellord1])).

thf('6',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v6_relat_2 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k3_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X10 ) @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ( X10 = X11 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( v6_relat_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
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

thf('12',plain,(
    ! [X6: $i] :
      ( ~ ( v2_wellord1 @ X6 )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('13',plain,
    ( ( v6_relat_2 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v6_relat_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ( sk_A = sk_B_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) )
        <=> ( ( A = B )
            | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_wellord1 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_wellord1 @ X20 @ X22 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X20 @ X21 ) @ ( k1_wellord1 @ X20 @ X22 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_wellord1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t29_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X14 @ X13 ) @ X12 )
        = ( k2_wellord1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_wellord1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
        = ( k2_wellord1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf(t35_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) )
       => ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A )
          = ( k1_wellord1 @ C @ A ) ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_wellord1 @ X17 @ X19 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X19 ) ) @ X18 )
        = ( k1_wellord1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_1 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_1 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_wellord1 @ X27 )
      | ~ ( r4_wellord1 @ X27 @ ( k2_wellord1 @ X27 @ ( k1_wellord1 @ X27 @ X28 ) ) )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('51',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_wellord1 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k3_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X22 @ ( k3_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_wellord1 @ X20 @ X22 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X20 @ X21 ) @ ( k1_wellord1 @ X20 @ X22 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_wellord1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ~ ( v2_wellord1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X14 @ X13 ) @ X12 )
        = ( k2_wellord1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t29_wellord1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_wellord1 @ X17 @ X19 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X19 ) ) @ X18 )
        = ( k1_wellord1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ sk_A )
    = ( k1_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_wellord1 @ X27 )
      | ~ ( r4_wellord1 @ X27 @ ( k2_wellord1 @ X27 @ ( k1_wellord1 @ X27 @ X28 ) ) )
      | ~ ( r2_hidden @ X28 @ ( k3_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('88',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('92',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r4_wellord1 @ X25 @ X26 )
      | ~ ( r4_wellord1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['89','100','101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','102'])).

thf('104',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('105',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['111','112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mksDjJdEeG
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 212 iterations in 0.267s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.51/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.72  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.51/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.51/0.72  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.51/0.72  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.51/0.72  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.51/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.72  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.51/0.72  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.51/0.72  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.51/0.72  thf(t32_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ B ) =>
% 0.51/0.72       ( ( v2_wellord1 @ B ) => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ))).
% 0.51/0.72  thf('0', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X15)
% 0.51/0.72          | (v2_wellord1 @ (k2_wellord1 @ X15 @ X16))
% 0.51/0.72          | ~ (v1_relat_1 @ X15))),
% 0.51/0.72      inference('cnf', [status(esa)], [t32_wellord1])).
% 0.51/0.72  thf(dt_k2_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.51/0.72  thf(t40_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ B ) =>
% 0.51/0.72       ( ( v2_wellord1 @ B ) =>
% 0.51/0.72         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.51/0.72           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.51/0.72  thf('2', plain,
% 0.51/0.72      (![X23 : $i, X24 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X23)
% 0.51/0.72          | ((k3_relat_1 @ (k2_wellord1 @ X23 @ (k1_wellord1 @ X23 @ X24)))
% 0.51/0.72              = (k1_wellord1 @ X23 @ X24))
% 0.51/0.72          | ~ (v1_relat_1 @ X23))),
% 0.51/0.72      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X15)
% 0.51/0.72          | (v2_wellord1 @ (k2_wellord1 @ X15 @ X16))
% 0.51/0.72          | ~ (v1_relat_1 @ X15))),
% 0.51/0.72      inference('cnf', [status(esa)], [t32_wellord1])).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (![X23 : $i, X24 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X23)
% 0.51/0.72          | ((k3_relat_1 @ (k2_wellord1 @ X23 @ (k1_wellord1 @ X23 @ X24)))
% 0.51/0.72              = (k1_wellord1 @ X23 @ X24))
% 0.51/0.72          | ~ (v1_relat_1 @ X23))),
% 0.51/0.72      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.51/0.72  thf(t58_wellord1, conjecture,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ C ) =>
% 0.51/0.72       ( ~( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.51/0.72            ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & ( ( A ) != ( B ) ) & 
% 0.51/0.72            ( r4_wellord1 @
% 0.51/0.72              ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ 
% 0.51/0.72              ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.72        ( ( v1_relat_1 @ C ) =>
% 0.51/0.72          ( ~( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.51/0.72               ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & ( ( A ) != ( B ) ) & 
% 0.51/0.72               ( r4_wellord1 @
% 0.51/0.72                 ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ 
% 0.51/0.72                 ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t58_wellord1])).
% 0.51/0.72  thf('6', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('7', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(l4_wellord1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ( v6_relat_2 @ A ) <=>
% 0.51/0.72         ( ![B:$i,C:$i]:
% 0.51/0.72           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.51/0.72                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.51/0.72                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.51/0.72                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.51/0.72  thf('8', plain,
% 0.51/0.72      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.72         (~ (v6_relat_2 @ X9)
% 0.51/0.72          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ X11 @ X10) @ X9)
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.51/0.72          | ((X10) = (X11))
% 0.51/0.72          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.51/0.72          | ~ (v1_relat_1 @ X9))),
% 0.51/0.72      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72          | ((sk_A) = (X0))
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1)
% 0.51/0.72          | ~ (v6_relat_2 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.72  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(d4_wellord1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ( v2_wellord1 @ A ) <=>
% 0.51/0.72         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.51/0.72           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      (![X6 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X6) | (v6_relat_2 @ X6) | ~ (v1_relat_1 @ X6))),
% 0.51/0.72      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.51/0.72  thf('13', plain, (((v6_relat_2 @ sk_C_1) | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.72  thf('14', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('15', plain, ((v6_relat_2 @ sk_C_1)),
% 0.51/0.72      inference('demod', [status(thm)], ['13', '14'])).
% 0.51/0.72  thf('16', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72          | ((sk_A) = (X0))
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.51/0.72          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['9', '10', '15'])).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.51/0.72        | ((sk_A) = (sk_B_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['6', '16'])).
% 0.51/0.72  thf('18', plain, (((sk_A) != (sk_B_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.51/0.72  thf(d1_wellord1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ![B:$i,C:$i]:
% 0.51/0.72         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.51/0.72           ( ![D:$i]:
% 0.51/0.72             ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.72               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.51/0.72         (((X3) != (k1_wellord1 @ X2 @ X1))
% 0.51/0.72          | (r2_hidden @ X5 @ X3)
% 0.51/0.72          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.51/0.72          | ((X5) = (X1))
% 0.51/0.72          | ~ (v1_relat_1 @ X2))),
% 0.51/0.72      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X2)
% 0.51/0.72          | ((X5) = (X1))
% 0.51/0.72          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.51/0.72          | (r2_hidden @ X5 @ (k1_wellord1 @ X2 @ X1)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.51/0.72  thf('22', plain,
% 0.51/0.72      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | ((sk_B_1) = (sk_A))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['19', '21'])).
% 0.51/0.72  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | ((sk_B_1) = (sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.51/0.72  thf('25', plain, (((sk_A) != (sk_B_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X2)
% 0.51/0.72          | ((X5) = (X1))
% 0.51/0.72          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.51/0.72          | (r2_hidden @ X5 @ (k1_wellord1 @ X2 @ X1)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ((sk_A) = (sk_B_1))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.51/0.72  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('30', plain,
% 0.51/0.72      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ((sk_A) = (sk_B_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf('31', plain, (((sk_A) != (sk_B_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('32', plain,
% 0.51/0.72      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.51/0.72  thf('33', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t38_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ C ) =>
% 0.51/0.72       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.51/0.72           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.51/0.72         ( ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) <=>
% 0.51/0.72           ( ( ( A ) = ( B ) ) | ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X20)
% 0.51/0.72          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.51/0.72          | ~ (r2_hidden @ X22 @ (k3_relat_1 @ X20))
% 0.51/0.72          | ~ (r2_hidden @ X21 @ (k1_wellord1 @ X20 @ X22))
% 0.51/0.72          | (r1_tarski @ (k1_wellord1 @ X20 @ X21) @ (k1_wellord1 @ X20 @ X22))
% 0.51/0.72          | ~ (v1_relat_1 @ X20))),
% 0.51/0.72      inference('cnf', [status(esa)], [t38_wellord1])).
% 0.51/0.72  thf('35', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.51/0.72             (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72          | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.72  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('37', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('38', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.51/0.72           (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.51/0.72  thf('39', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.51/0.72           (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['32', '38'])).
% 0.51/0.72  thf('40', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('41', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_B_1) @ 
% 0.51/0.72           (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['39', '40'])).
% 0.51/0.72  thf(t29_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ C ) =>
% 0.51/0.72       ( ( r1_tarski @ A @ B ) =>
% 0.51/0.72         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.51/0.72           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.51/0.72  thf('42', plain,
% 0.51/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X12 @ X13)
% 0.51/0.72          | ~ (v1_relat_1 @ X14)
% 0.51/0.72          | ((k2_wellord1 @ (k2_wellord1 @ X14 @ X13) @ X12)
% 0.51/0.72              = (k2_wellord1 @ X14 @ X12)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t29_wellord1])).
% 0.51/0.72  thf('43', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72          | ((k2_wellord1 @ 
% 0.51/0.72              (k2_wellord1 @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72              (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72              = (k2_wellord1 @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72          | ~ (v1_relat_1 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.51/0.72  thf(t35_wellord1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ C ) =>
% 0.51/0.72       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) =>
% 0.51/0.72         ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A ) =
% 0.51/0.72           ( k1_wellord1 @ C @ A ) ) ) ))).
% 0.51/0.72  thf('45', plain,
% 0.51/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X17)
% 0.51/0.72          | ~ (r2_hidden @ X18 @ (k1_wellord1 @ X17 @ X19))
% 0.51/0.72          | ((k1_wellord1 @ (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X19)) @ 
% 0.51/0.72              X18) = (k1_wellord1 @ X17 @ X18))
% 0.51/0.72          | ~ (v1_relat_1 @ X17))),
% 0.51/0.72      inference('cnf', [status(esa)], [t35_wellord1])).
% 0.51/0.72  thf('46', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ((k1_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B_1)
% 0.51/0.72            = (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.72  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('48', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('49', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ((k1_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B_1)
% 0.51/0.72            = (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.51/0.72  thf(t57_wellord1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ( v2_wellord1 @ A ) =>
% 0.51/0.72         ( ![B:$i]:
% 0.51/0.72           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.51/0.72                ( r4_wellord1 @
% 0.51/0.72                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('50', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X27)
% 0.51/0.72          | ~ (r4_wellord1 @ X27 @ 
% 0.51/0.72               (k2_wellord1 @ X27 @ (k1_wellord1 @ X27 @ X28)))
% 0.51/0.72          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X27))
% 0.51/0.72          | ~ (v1_relat_1 @ X27))),
% 0.51/0.72      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.51/0.72  thf('51', plain,
% 0.51/0.72      ((~ (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72           (k2_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72            (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.72  thf('52', plain,
% 0.51/0.72      ((~ (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['43', '51'])).
% 0.51/0.72  thf('53', plain,
% 0.51/0.72      ((r4_wellord1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('54', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('55', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.51/0.72  thf('56', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('simplify', [status(thm)], ['55'])).
% 0.51/0.72  thf('57', plain,
% 0.51/0.72      ((~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v2_wellord1 @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['5', '56'])).
% 0.51/0.72  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('59', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('60', plain,
% 0.51/0.72      ((~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.51/0.72  thf('61', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v2_wellord1 @ sk_C_1)
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['4', '60'])).
% 0.51/0.72  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('63', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('64', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.51/0.72  thf('65', plain,
% 0.51/0.72      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.51/0.72  thf('66', plain,
% 0.51/0.72      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('clc', [status(thm)], ['64', '65'])).
% 0.51/0.72  thf('67', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['3', '66'])).
% 0.51/0.72  thf('68', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('69', plain, ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.72  thf('70', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('71', plain,
% 0.51/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X20)
% 0.51/0.72          | ~ (r2_hidden @ X21 @ (k3_relat_1 @ X20))
% 0.51/0.72          | ~ (r2_hidden @ X22 @ (k3_relat_1 @ X20))
% 0.51/0.72          | ~ (r2_hidden @ X21 @ (k1_wellord1 @ X20 @ X22))
% 0.51/0.72          | (r1_tarski @ (k1_wellord1 @ X20 @ X21) @ (k1_wellord1 @ X20 @ X22))
% 0.51/0.72          | ~ (v1_relat_1 @ X20))),
% 0.51/0.72      inference('cnf', [status(esa)], [t38_wellord1])).
% 0.51/0.72  thf('72', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72          | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.51/0.72             (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72          | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.51/0.72  thf('73', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('74', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('75', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.51/0.72           (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ X0))
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.51/0.72  thf('76', plain,
% 0.51/0.72      ((~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))
% 0.51/0.72        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.51/0.72           (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['69', '75'])).
% 0.51/0.72  thf('77', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('78', plain,
% 0.51/0.72      ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.51/0.72        (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['76', '77'])).
% 0.51/0.72  thf('79', plain,
% 0.51/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X12 @ X13)
% 0.51/0.72          | ~ (v1_relat_1 @ X14)
% 0.51/0.72          | ((k2_wellord1 @ (k2_wellord1 @ X14 @ X13) @ X12)
% 0.51/0.72              = (k2_wellord1 @ X14 @ X12)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t29_wellord1])).
% 0.51/0.72  thf('80', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (((k2_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72            (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72            = (k2_wellord1 @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72          | ~ (v1_relat_1 @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['78', '79'])).
% 0.51/0.72  thf('81', plain, ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.72  thf('82', plain,
% 0.51/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X17)
% 0.51/0.72          | ~ (r2_hidden @ X18 @ (k1_wellord1 @ X17 @ X19))
% 0.51/0.72          | ((k1_wellord1 @ (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X19)) @ 
% 0.51/0.72              X18) = (k1_wellord1 @ X17 @ X18))
% 0.51/0.72          | ~ (v1_relat_1 @ X17))),
% 0.51/0.72      inference('cnf', [status(esa)], [t35_wellord1])).
% 0.51/0.72  thf('83', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ((k1_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ sk_A)
% 0.51/0.72            = (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.51/0.72        | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['81', '82'])).
% 0.51/0.72  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('85', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('86', plain,
% 0.51/0.72      (((k1_wellord1 @ 
% 0.51/0.72         (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ sk_A)
% 0.51/0.72         = (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.51/0.72  thf('87', plain,
% 0.51/0.72      (![X27 : $i, X28 : $i]:
% 0.51/0.72         (~ (v2_wellord1 @ X27)
% 0.51/0.72          | ~ (r4_wellord1 @ X27 @ 
% 0.51/0.72               (k2_wellord1 @ X27 @ (k1_wellord1 @ X27 @ X28)))
% 0.51/0.72          | ~ (r2_hidden @ X28 @ (k3_relat_1 @ X27))
% 0.51/0.72          | ~ (v1_relat_1 @ X27))),
% 0.51/0.72      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.51/0.72  thf('88', plain,
% 0.51/0.72      ((~ (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ 
% 0.51/0.72            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72            (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (r2_hidden @ sk_A @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['86', '87'])).
% 0.51/0.72  thf('89', plain,
% 0.51/0.72      ((~ (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (r2_hidden @ sk_A @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['80', '88'])).
% 0.51/0.72  thf('90', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.51/0.72  thf('91', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.51/0.72  thf('92', plain,
% 0.51/0.72      ((r4_wellord1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.51/0.72        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t50_wellord1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( v1_relat_1 @ B ) =>
% 0.51/0.72           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.51/0.72  thf('93', plain,
% 0.51/0.72      (![X25 : $i, X26 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X25)
% 0.51/0.72          | (r4_wellord1 @ X25 @ X26)
% 0.51/0.72          | ~ (r4_wellord1 @ X26 @ X25)
% 0.51/0.72          | ~ (v1_relat_1 @ X26))),
% 0.51/0.72      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.51/0.72  thf('94', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['92', '93'])).
% 0.51/0.72  thf('95', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['91', '94'])).
% 0.51/0.72  thf('96', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('97', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('demod', [status(thm)], ['95', '96'])).
% 0.51/0.72  thf('98', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | (r4_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['90', '97'])).
% 0.51/0.72  thf('99', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('100', plain,
% 0.51/0.72      ((r4_wellord1 @ 
% 0.51/0.72        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.51/0.72        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.51/0.72      inference('demod', [status(thm)], ['98', '99'])).
% 0.51/0.72  thf('101', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('102', plain,
% 0.51/0.72      ((~ (v2_wellord1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (r2_hidden @ sk_A @ 
% 0.51/0.72             (k3_relat_1 @ 
% 0.51/0.72              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('demod', [status(thm)], ['89', '100', '101'])).
% 0.51/0.72  thf('103', plain,
% 0.51/0.72      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.51/0.72        | ~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v2_wellord1 @ sk_C_1)
% 0.51/0.72        | ~ (v1_relat_1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['2', '102'])).
% 0.51/0.72  thf('104', plain, ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.51/0.72  thf('105', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('106', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('107', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ 
% 0.51/0.72           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.51/0.72  thf('108', plain,
% 0.51/0.72      ((~ (v1_relat_1 @ sk_C_1)
% 0.51/0.72        | ~ (v2_wellord1 @ 
% 0.51/0.72             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['1', '107'])).
% 0.51/0.72  thf('109', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('110', plain,
% 0.51/0.72      (~ (v2_wellord1 @ 
% 0.51/0.72          (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.51/0.72      inference('demod', [status(thm)], ['108', '109'])).
% 0.51/0.72  thf('111', plain, ((~ (v1_relat_1 @ sk_C_1) | ~ (v2_wellord1 @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['0', '110'])).
% 0.51/0.72  thf('112', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('113', plain, ((v2_wellord1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('114', plain, ($false),
% 0.51/0.72      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
