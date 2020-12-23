%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dpQtrKNXl6

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:36 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 436 expanded)
%              Number of leaves         :   29 ( 135 expanded)
%              Depth                    :   34
%              Number of atoms          : 1330 (6995 expanded)
%              Number of equality atoms :   34 ( 265 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

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

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_wellord1 @ X22 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X22 @ ( k1_wellord1 @ X22 @ X23 ) ) )
        = ( k1_wellord1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_wellord1 @ X22 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X22 @ ( k1_wellord1 @ X22 @ X23 ) ) )
        = ( k1_wellord1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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

thf(t35_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) )
       => ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A )
          = ( k1_wellord1 @ C @ A ) ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_wellord1 @ X19 @ X21 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X19 @ ( k1_wellord1 @ X19 @ X21 ) ) @ X20 )
        = ( k1_wellord1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_1 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_1 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_wellord1 @ X22 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X22 @ ( k1_wellord1 @ X22 @ X23 ) ) )
        = ( k1_wellord1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X12 @ X13 ) @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t29_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X16 @ X15 ) @ X14 )
        = ( k2_wellord1 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t29_wellord1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X3 @ ( k1_wellord1 @ X1 @ X0 ) ) @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X2 ) )
        = ( k2_wellord1 @ X3 @ ( k1_wellord1 @ ( k2_wellord1 @ X1 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_wellord1 @ X26 )
      | ~ ( r4_wellord1 @ X26 @ ( k2_wellord1 @ X26 @ ( k1_wellord1 @ X26 @ X27 ) ) )
      | ~ ( r2_hidden @ X27 @ ( k3_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v2_wellord1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) ) )
      | ~ ( v2_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_wellord1 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_wellord1 @ X19 @ X21 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X19 @ ( k1_wellord1 @ X19 @ X21 ) ) @ X20 )
        = ( k1_wellord1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ sk_A )
    = ( k1_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ ( k2_wellord1 @ X2 @ ( k1_wellord1 @ X2 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('73',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('76',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r4_wellord1 @ X24 @ X25 )
      | ~ ( r4_wellord1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['73','84','85','86'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','87'])).

thf('89',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('90',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dpQtrKNXl6
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 191 iterations in 0.155s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.61  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.41/0.61  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.41/0.61  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.41/0.61  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.41/0.61  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.41/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.61  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.41/0.61  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.41/0.61  thf(dt_k2_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.41/0.61  thf(t32_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( v2_wellord1 @ B ) => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X17)
% 0.41/0.61          | (v2_wellord1 @ (k2_wellord1 @ X17 @ X18))
% 0.41/0.61          | ~ (v1_relat_1 @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t32_wellord1])).
% 0.41/0.61  thf(t40_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( v2_wellord1 @ B ) =>
% 0.41/0.61         ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) ) =
% 0.41/0.61           ( k1_wellord1 @ B @ A ) ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X22)
% 0.41/0.61          | ((k3_relat_1 @ (k2_wellord1 @ X22 @ (k1_wellord1 @ X22 @ X23)))
% 0.41/0.61              = (k1_wellord1 @ X22 @ X23))
% 0.41/0.61          | ~ (v1_relat_1 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X17)
% 0.41/0.61          | (v2_wellord1 @ (k2_wellord1 @ X17 @ X18))
% 0.41/0.61          | ~ (v1_relat_1 @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t32_wellord1])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X22)
% 0.41/0.61          | ((k3_relat_1 @ (k2_wellord1 @ X22 @ (k1_wellord1 @ X22 @ X23)))
% 0.41/0.61              = (k1_wellord1 @ X22 @ X23))
% 0.41/0.61          | ~ (v1_relat_1 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.41/0.61  thf(t58_wellord1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ~( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.41/0.61            ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & ( ( A ) != ( B ) ) & 
% 0.41/0.61            ( r4_wellord1 @
% 0.41/0.61              ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ 
% 0.41/0.61              ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( v1_relat_1 @ C ) =>
% 0.41/0.61          ( ~( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.41/0.61               ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & ( ( A ) != ( B ) ) & 
% 0.41/0.61               ( r4_wellord1 @
% 0.41/0.61                 ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ A ) ) @ 
% 0.41/0.61                 ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t58_wellord1])).
% 0.41/0.61  thf('6', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('7', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(l4_wellord1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( v6_relat_2 @ A ) <=>
% 0.41/0.61         ( ![B:$i,C:$i]:
% 0.41/0.61           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.41/0.61                ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & ( ( B ) != ( C ) ) & 
% 0.41/0.61                ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) & 
% 0.41/0.61                ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.61         (~ (v6_relat_2 @ X9)
% 0.41/0.61          | ~ (r2_hidden @ X10 @ (k3_relat_1 @ X9))
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X11 @ X10) @ X9)
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.41/0.61          | ((X10) = (X11))
% 0.41/0.61          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X9))
% 0.41/0.61          | ~ (v1_relat_1 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [l4_wellord1])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.41/0.61          | ((sk_A) = (X0))
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1)
% 0.41/0.61          | ~ (v6_relat_2 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d4_wellord1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( v2_wellord1 @ A ) <=>
% 0.41/0.61         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.41/0.61           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X6 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X6) | (v6_relat_2 @ X6) | ~ (v1_relat_1 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.41/0.61  thf('13', plain, (((v6_relat_2 @ sk_C_1) | ~ (v2_wellord1 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('15', plain, ((v6_relat_2 @ sk_C_1)),
% 0.41/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ (k3_relat_1 @ sk_C_1))
% 0.41/0.61          | ((sk_A) = (X0))
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_C_1)
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10', '15'])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.41/0.61        | ((sk_A) = (sk_B_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '16'])).
% 0.41/0.61  thf('18', plain, (((sk_A) != (sk_B_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_A) @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf(d1_wellord1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ![B:$i,C:$i]:
% 0.41/0.61         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.41/0.61           ( ![D:$i]:
% 0.41/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.61               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.61         (((X3) != (k1_wellord1 @ X2 @ X1))
% 0.41/0.61          | (r2_hidden @ X5 @ X3)
% 0.41/0.61          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.41/0.61          | ((X5) = (X1))
% 0.41/0.61          | ~ (v1_relat_1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X2)
% 0.41/0.61          | ((X5) = (X1))
% 0.41/0.61          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.41/0.61          | (r2_hidden @ X5 @ (k1_wellord1 @ X2 @ X1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | ((sk_B_1) = (sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '21'])).
% 0.41/0.61  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | ((sk_B_1) = (sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain, (((sk_A) != (sk_B_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B_1) @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X2)
% 0.41/0.61          | ((X5) = (X1))
% 0.41/0.61          | ~ (r2_hidden @ (k4_tarski @ X5 @ X1) @ X2)
% 0.41/0.61          | (r2_hidden @ X5 @ (k1_wellord1 @ X2 @ X1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ((sk_A) = (sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.61  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ((sk_A) = (sk_B_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.61  thf('31', plain, (((sk_A) != (sk_B_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf(t35_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) ) =>
% 0.41/0.61         ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A ) =
% 0.41/0.61           ( k1_wellord1 @ C @ A ) ) ) ))).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X19)
% 0.41/0.61          | ~ (r2_hidden @ X20 @ (k1_wellord1 @ X19 @ X21))
% 0.41/0.61          | ((k1_wellord1 @ (k2_wellord1 @ X19 @ (k1_wellord1 @ X19 @ X21)) @ 
% 0.41/0.61              X20) = (k1_wellord1 @ X19 @ X20))
% 0.41/0.61          | ~ (v1_relat_1 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t35_wellord1])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ((k1_wellord1 @ 
% 0.41/0.61            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B_1)
% 0.41/0.61            = (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('36', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ((k1_wellord1 @ 
% 0.41/0.61            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B_1)
% 0.41/0.61            = (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X22)
% 0.41/0.61          | ((k3_relat_1 @ (k2_wellord1 @ X22 @ (k1_wellord1 @ X22 @ X23)))
% 0.41/0.61              = (k1_wellord1 @ X22 @ X23))
% 0.41/0.61          | ~ (v1_relat_1 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [t40_wellord1])).
% 0.41/0.61  thf(t13_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ))).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X12 : $i, X13 : $i]:
% 0.41/0.61         ((r1_tarski @ (k1_wellord1 @ X12 @ X13) @ (k3_relat_1 @ X12))
% 0.41/0.61          | ~ (v1_relat_1 @ X12))),
% 0.41/0.61      inference('cnf', [status(esa)], [t13_wellord1])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ 
% 0.41/0.61           (k1_wellord1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0)) @ X2) @ 
% 0.41/0.61           (k1_wellord1 @ X1 @ X0))
% 0.41/0.61          | ~ (v1_relat_1 @ X1)
% 0.41/0.61          | ~ (v2_wellord1 @ X1)
% 0.41/0.61          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X1)
% 0.41/0.61          | ~ (v2_wellord1 @ X1)
% 0.41/0.61          | ~ (v1_relat_1 @ X1)
% 0.41/0.61          | (r1_tarski @ 
% 0.41/0.61             (k1_wellord1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0)) @ X2) @ 
% 0.41/0.61             (k1_wellord1 @ X1 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ 
% 0.41/0.61           (k1_wellord1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0)) @ X2) @ 
% 0.41/0.61           (k1_wellord1 @ X1 @ X0))
% 0.41/0.61          | ~ (v2_wellord1 @ X1)
% 0.41/0.61          | ~ (v1_relat_1 @ X1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['42'])).
% 0.41/0.61  thf(t29_wellord1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ( r1_tarski @ A @ B ) =>
% 0.41/0.61         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.41/0.61           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X14 @ X15)
% 0.41/0.61          | ~ (v1_relat_1 @ X16)
% 0.41/0.61          | ((k2_wellord1 @ (k2_wellord1 @ X16 @ X15) @ X14)
% 0.41/0.61              = (k2_wellord1 @ X16 @ X14)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t29_wellord1])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X1)
% 0.41/0.61          | ~ (v2_wellord1 @ X1)
% 0.41/0.61          | ((k2_wellord1 @ (k2_wellord1 @ X3 @ (k1_wellord1 @ X1 @ X0)) @ 
% 0.41/0.61              (k1_wellord1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0)) @ X2))
% 0.41/0.61              = (k2_wellord1 @ X3 @ 
% 0.41/0.61                 (k1_wellord1 @ (k2_wellord1 @ X1 @ (k1_wellord1 @ X1 @ X0)) @ 
% 0.41/0.61                  X2)))
% 0.41/0.61          | ~ (v1_relat_1 @ X3))),
% 0.41/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.61  thf(t57_wellord1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( v2_wellord1 @ A ) =>
% 0.41/0.61         ( ![B:$i]:
% 0.41/0.61           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.41/0.61                ( r4_wellord1 @
% 0.41/0.61                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X26 : $i, X27 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X26)
% 0.41/0.61          | ~ (r4_wellord1 @ X26 @ 
% 0.41/0.61               (k2_wellord1 @ X26 @ (k1_wellord1 @ X26 @ X27)))
% 0.41/0.61          | ~ (r2_hidden @ X27 @ (k3_relat_1 @ X26))
% 0.41/0.61          | ~ (v1_relat_1 @ X26))),
% 0.41/0.61      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r4_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ 
% 0.41/0.61             (k2_wellord1 @ X2 @ 
% 0.41/0.61              (k1_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ X0)))
% 0.41/0.61          | ~ (v1_relat_1 @ X2)
% 0.41/0.61          | ~ (v2_wellord1 @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ 
% 0.41/0.61               (k3_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1))))
% 0.41/0.61          | ~ (v2_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ 
% 0.41/0.61               (k3_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1))))
% 0.41/0.61          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)))
% 0.41/0.61          | ~ (v2_wellord1 @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ X2)
% 0.41/0.61          | ~ (r4_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ 
% 0.41/0.61               (k2_wellord1 @ X2 @ 
% 0.41/0.61                (k1_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ 
% 0.41/0.61                 X0))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      ((~ (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (r2_hidden @ sk_B_1 @ 
% 0.41/0.61             (k3_relat_1 @ 
% 0.41/0.61              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['37', '48'])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      ((r4_wellord1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.41/0.61        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('52', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (r2_hidden @ sk_B_1 @ 
% 0.41/0.61             (k3_relat_1 @ 
% 0.41/0.61              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['5', '53'])).
% 0.41/0.61  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('56', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '57'])).
% 0.41/0.61  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('60', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (((r2_hidden @ sk_B_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['61', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '63'])).
% 0.41/0.61  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('66', plain, ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ X19)
% 0.41/0.61          | ~ (r2_hidden @ X20 @ (k1_wellord1 @ X19 @ X21))
% 0.41/0.61          | ((k1_wellord1 @ (k2_wellord1 @ X19 @ (k1_wellord1 @ X19 @ X21)) @ 
% 0.41/0.61              X20) = (k1_wellord1 @ X19 @ X20))
% 0.41/0.61          | ~ (v1_relat_1 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t35_wellord1])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ((k1_wellord1 @ 
% 0.41/0.61            (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ sk_A)
% 0.41/0.61            = (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.41/0.61  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('70', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (((k1_wellord1 @ 
% 0.41/0.61         (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ sk_A)
% 0.41/0.61         = (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (v2_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ 
% 0.41/0.61               (k3_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1))))
% 0.41/0.61          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)))
% 0.41/0.61          | ~ (v2_wellord1 @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ X2)
% 0.41/0.61          | ~ (r4_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ 
% 0.41/0.61               (k2_wellord1 @ X2 @ 
% 0.41/0.61                (k1_wellord1 @ (k2_wellord1 @ X2 @ (k1_wellord1 @ X2 @ X1)) @ 
% 0.41/0.61                 X0))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      ((~ (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | ~ (r2_hidden @ sk_A @ 
% 0.41/0.61             (k3_relat_1 @ 
% 0.41/0.61              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k2_wellord1 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      ((r4_wellord1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.41/0.61        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t50_wellord1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( v1_relat_1 @ B ) =>
% 0.41/0.61           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X24)
% 0.41/0.61          | (r4_wellord1 @ X24 @ X25)
% 0.41/0.61          | ~ (r4_wellord1 @ X25 @ X24)
% 0.41/0.61          | ~ (v1_relat_1 @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '78'])).
% 0.41/0.61  thf('80', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | (r4_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['74', '81'])).
% 0.41/0.61  thf('83', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      ((r4_wellord1 @ 
% 0.41/0.61        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)) @ 
% 0.41/0.61        (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('86', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | ~ (r2_hidden @ sk_A @ 
% 0.41/0.61             (k3_relat_1 @ 
% 0.41/0.61              (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('demod', [status(thm)], ['73', '84', '85', '86'])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '87'])).
% 0.41/0.61  thf('89', plain, ((r2_hidden @ sk_A @ (k1_wellord1 @ sk_C_1 @ sk_B_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.41/0.61  thf('90', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('91', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      ((~ (v2_wellord1 @ 
% 0.41/0.61           (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61        | ~ (v2_wellord1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_relat_1 @ 
% 0.41/0.61             (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '92'])).
% 0.41/0.61  thf('94', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('95', plain, ((v2_wellord1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      (~ (v1_relat_1 @ (k2_wellord1 @ sk_C_1 @ (k1_wellord1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.41/0.61  thf('97', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '96'])).
% 0.41/0.61  thf('98', plain, ((v1_relat_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('99', plain, ($false), inference('demod', [status(thm)], ['97', '98'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
