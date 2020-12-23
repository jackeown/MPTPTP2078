%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0805+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EL8UiMog2K

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:30 EST 2020

% Result     : Theorem 25.22s
% Output     : Refutation 25.22s
% Verified   : 
% Statistics : Number of formulae       :  212 (3736 expanded)
%              Number of leaves         :   41 (1065 expanded)
%              Depth                    :   59
%              Number of atoms          : 2174 (60667 expanded)
%              Number of equality atoms :   37 (2305 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

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

thf('0',plain,(
    r2_hidden @ sk_B_2 @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v6_relat_2 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k3_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X13 )
      | ( X14 = X15 )
      | ~ ( r2_hidden @ X15 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( v6_relat_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X6: $i] :
      ( ~ ( v2_wellord1 @ X6 )
      | ( v6_relat_2 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('7',plain,
    ( ( v6_relat_2 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v6_relat_2 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_C_1 ) )
      | ( sk_A = X0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['3','4','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_2 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 )
    | ( sk_A = sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_2 @ sk_A ) @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_2 = sk_A )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( sk_B_2 = sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_1 )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( sk_A = sk_B_2 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_wellord1 @ X21 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf(t40_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_wellord1 @ X32 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X32 @ ( k1_wellord1 @ X32 @ X33 ) ) )
        = ( k1_wellord1 @ X32 @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf(t33_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( v2_wellord1 @ C )
       => ( r3_xboole_0 @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v2_wellord1 @ X23 )
      | ( r3_xboole_0 @ ( k1_wellord1 @ X23 @ X24 ) @ ( k1_wellord1 @ X23 @ X25 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t33_wellord1])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X8 @ X7 )
      | ~ ( r3_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t29_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X18 @ X17 ) @ X16 )
        = ( k2_wellord1 @ X18 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_wellord1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X3 @ ( k1_wellord1 @ X1 @ X0 ) ) @ ( k1_wellord1 @ X1 @ X2 ) )
        = ( k2_wellord1 @ X3 @ ( k1_wellord1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(t35_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k1_wellord1 @ C @ B ) ) )
       => ( ( k1_wellord1 @ ( k2_wellord1 @ C @ ( k1_wellord1 @ C @ B ) ) @ A )
          = ( k1_wellord1 @ C @ A ) ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_wellord1 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k1_wellord1 @ X26 @ X28 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X26 @ ( k1_wellord1 @ X26 @ X28 ) ) @ X27 )
        = ( k1_wellord1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_2 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B_2 )
      = ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_wellord1 @ X39 )
      | ~ ( r4_wellord1 @ X39 @ ( k2_wellord1 @ X39 @ ( k1_wellord1 @ X39 @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k3_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('43',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('62',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('65',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ( m1_subset_1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['27','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X2 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(eq_fact,[status(thm)],['69'])).

thf('71',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_wellord1 @ X1 )
      | ( m1_subset_1 @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_wellord1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ X2 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r2_hidden @ sk_B_2 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( X4 != X1 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('82',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_wellord1 @ X21 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('90',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('91',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_wellord1 @ X32 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X32 @ ( k1_wellord1 @ X32 @ X33 ) ) )
        = ( k1_wellord1 @ X32 @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t40_wellord1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ ( k1_wellord1 @ X1 @ X2 ) )
      | ~ ( v2_wellord1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X3 @ ( k1_wellord1 @ X1 @ X0 ) ) @ ( k1_wellord1 @ X1 @ X2 ) )
        = ( k2_wellord1 @ X3 @ ( k1_wellord1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('93',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('94',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_wellord1 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( k1_wellord1 @ X26 @ X28 ) )
      | ( ( k1_wellord1 @ ( k2_wellord1 @ X26 @ ( k1_wellord1 @ X26 @ X28 ) ) @ X27 )
        = ( k1_wellord1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_wellord1])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v2_wellord1 @ X39 )
      | ~ ( r4_wellord1 @ X39 @ ( k2_wellord1 @ X39 @ ( k1_wellord1 @ X39 @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ ( k3_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('100',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('104',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('105',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r4_wellord1 @ X37 @ X38 )
      | ~ ( r4_wellord1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    r4_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['101','112','113','114','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['90','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_wellord1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('129',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X29: $i,X31: $i] :
      ( ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ( m1_subset_1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('134',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ( m1_subset_1 @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','135'])).

thf('137',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( ( k1_wellord1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) @ sk_A )
      = ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('141',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('142',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('144',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ ( k2_wellord1 @ sk_C_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['142','147'])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['138','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('156',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    r2_hidden @ sk_A @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['26','156'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('159',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('163',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('164',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('167',plain,(
    v1_xboole_0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['162','167'])).

thf('169',plain,(
    $false ),
    inference('sup-',[status(thm)],['157','168'])).


%------------------------------------------------------------------------------
