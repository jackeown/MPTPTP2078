%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0734+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ngm5VeHVf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 22.15s
% Output     : Refutation 22.15s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 104 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  395 ( 715 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_C_61_type,type,(
    sk_C_61: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_32_type,type,(
    sk_B_32: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_13_type,type,(
    sk_A_13: $i )).

thf(t22_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ ( A @ B ) )
                  & ( r2_hidden @ ( B @ C ) ) )
               => ( r2_hidden @ ( A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r1_tarski @ ( A @ B ) )
                    & ( r2_hidden @ ( B @ C ) ) )
                 => ( r2_hidden @ ( A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_A_13 @ sk_C_61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3064: $i] :
      ( ( v1_ordinal1 @ X3064 )
      | ~ ( v3_ordinal1 @ X3064 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('2',plain,(
    r2_hidden @ ( sk_B_32 @ sk_C_61 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ ( B @ A ) )
         => ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X3067: $i,X3068: $i] :
      ( ~ ( r2_hidden @ ( X3067 @ X3068 ) )
      | ( r1_tarski @ ( X3067 @ X3068 ) )
      | ~ ( v1_ordinal1 @ X3068 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,
    ( ~ ( v1_ordinal1 @ sk_C_61 )
    | ( r1_tarski @ ( sk_B_32 @ sk_C_61 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v3_ordinal1 @ sk_C_61 )
    | ( r1_tarski @ ( sk_B_32 @ sk_C_61 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_C_61 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( sk_B_32 @ sk_C_61 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('9',plain,
    ( ( sk_B_32 = sk_C_61 )
    | ( r2_xboole_0 @ ( sk_B_32 @ sk_C_61 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( sk_A_13 @ sk_B_32 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ C ) ) )
     => ( r2_xboole_0 @ ( A @ C ) ) ) )).

thf('11',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ~ ( r1_tarski @ ( X94 @ X95 ) )
      | ~ ( r2_xboole_0 @ ( X95 @ X96 ) )
      | ( r2_xboole_0 @ ( X94 @ X96 ) ) ) ),
    inference(cnf,[status(esa)],[l58_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( sk_A_13 @ X0 ) )
      | ~ ( r2_xboole_0 @ ( sk_B_32 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_32 = sk_C_61 )
    | ( r2_xboole_0 @ ( sk_A_13 @ sk_C_61 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ ( A @ B ) )
           => ( r2_hidden @ ( A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X3088: $i,X3089: $i] :
      ( ~ ( v3_ordinal1 @ X3088 )
      | ( r2_hidden @ ( X3089 @ X3088 ) )
      | ~ ( r2_xboole_0 @ ( X3089 @ X3088 ) )
      | ~ ( v1_ordinal1 @ X3089 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('15',plain,
    ( ( sk_B_32 = sk_C_61 )
    | ~ ( v1_ordinal1 @ sk_A_13 )
    | ( r2_hidden @ ( sk_A_13 @ sk_C_61 ) )
    | ~ ( v3_ordinal1 @ sk_C_61 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_ordinal1 @ sk_A_13 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_ordinal1 @ sk_C_61 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_32 = sk_C_61 )
    | ( r2_hidden @ ( sk_A_13 @ sk_C_61 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ ( sk_B_32 @ sk_C_61 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( sk_B_32 @ sk_C_61 ) )
    = sk_C_61 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('22',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( sk_B_32 @ sk_C_61 ) )
    = sk_B_32 ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B @ ( k6_relat_1 @ A ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X2948: $i,X2949: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X2949 @ ( k6_relat_1 @ X2948 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( X2948 @ X2949 ) ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( B @ A ) ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X2931: $i,X2932: $i] :
      ( ~ ( v1_relat_1 @ X2931 )
      | ~ ( v1_funct_1 @ X2931 )
      | ( r1_tarski @ ( k2_relat_1 @ X2931 @ ( k1_relat_1 @ X2932 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( X2931 @ X2932 ) ) )
       != ( k1_relat_1 @ X2931 ) )
      | ~ ( v1_funct_1 @ X2932 )
      | ~ ( v1_relat_1 @ X2932 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X2692: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X2692 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X2692: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X2692 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( X1 @ X0 ) )
       != X0 )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','32','33','34'])).

thf('36',plain,
    ( ( sk_B_32 != sk_C_61 )
    | ( r1_tarski @ ( sk_C_61 @ sk_B_32 ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_B_32 @ sk_C_61 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) )).

thf('38',plain,(
    ! [X3108: $i,X3109: $i] :
      ( ~ ( r2_hidden @ ( X3108 @ X3109 ) )
      | ~ ( r1_tarski @ ( X3109 @ X3108 ) ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ~ ( r1_tarski @ ( sk_C_61 @ sk_B_32 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B_32 != sk_C_61 ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_A_13 @ sk_C_61 ) ),
    inference('simplify_reflect-',[status(thm)],['18','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
