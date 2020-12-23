%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQrtO20SY7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:21 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  247 (1539 expanded)
%              Number of leaves         :   30 ( 461 expanded)
%              Depth                    :   39
%              Number of atoms          : 2618 (20720 expanded)
%              Number of equality atoms :   82 ( 481 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t171_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
            <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
              <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('7',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('24',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X30 @ X29 ) @ X31 )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('35',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('45',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('57',plain,
    ( ( ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_C
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('64',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('73',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('86',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('88',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('90',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X30 @ X29 ) @ X31 )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('109',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','119'])).

thf('121',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('128',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','128'])).

thf('130',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('131',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('132',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('133',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('134',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('138',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('139',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ sk_C )
        = sk_C )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k2_xboole_0 @ sk_C @ sk_C )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_C )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( sk_C
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130','143','144'])).

thf('146',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('147',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('148',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_C ) @ sk_A )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['145','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('155',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_C ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['71','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('160',plain,
    ( ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_C ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('163',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('164',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('165',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['162','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('172',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['161','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['160','175'])).

thf('177',plain,
    ( ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('181',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('182',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('183',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('186',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( sk_C
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130','143','144'])).

thf('190',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('192',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['190','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ~ ( v1_funct_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','196'])).

thf('198',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('199',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ~ ( v1_funct_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_C ) )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_C ) )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['188','201'])).

thf('203',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('204',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('205',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['181','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','179','180','208'])).

thf('210',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('214',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','39','40','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQrtO20SY7
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.50/2.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.50/2.69  % Solved by: fo/fo7.sh
% 2.50/2.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.50/2.69  % done 1615 iterations in 2.233s
% 2.50/2.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.50/2.69  % SZS output start Refutation
% 2.50/2.69  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.50/2.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.50/2.69  thf(sk_A_type, type, sk_A: $i).
% 2.50/2.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.50/2.69  thf(sk_C_type, type, sk_C: $i).
% 2.50/2.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.50/2.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.50/2.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.50/2.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.50/2.69  thf(sk_B_type, type, sk_B: $i).
% 2.50/2.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.50/2.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.50/2.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.50/2.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.50/2.69  thf(t171_funct_1, conjecture,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.50/2.69       ( ![B:$i]:
% 2.50/2.69         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.50/2.69           ( ![C:$i]:
% 2.50/2.69             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 2.50/2.69               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 2.50/2.69                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 2.50/2.69  thf(zf_stmt_0, negated_conjecture,
% 2.50/2.69    (~( ![A:$i]:
% 2.50/2.69        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.50/2.69          ( ![B:$i]:
% 2.50/2.69            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.50/2.69              ( ![C:$i]:
% 2.50/2.69                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 2.50/2.69                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 2.50/2.69                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 2.50/2.69    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 2.50/2.69  thf('0', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 2.50/2.69        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('1', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.50/2.69       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.50/2.69      inference('split', [status(esa)], ['0'])).
% 2.50/2.69  thf(t182_relat_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) =>
% 2.50/2.69       ( ![B:$i]:
% 2.50/2.69         ( ( v1_relat_1 @ B ) =>
% 2.50/2.69           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.50/2.69             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.50/2.69  thf('2', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf(t44_relat_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) =>
% 2.50/2.69       ( ![B:$i]:
% 2.50/2.69         ( ( v1_relat_1 @ B ) =>
% 2.50/2.69           ( r1_tarski @
% 2.50/2.69             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 2.50/2.69  thf('3', plain,
% 2.50/2.69      (![X16 : $i, X17 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X16)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 2.50/2.69             (k1_relat_1 @ X17))
% 2.50/2.69          | ~ (v1_relat_1 @ X17))),
% 2.50/2.69      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.50/2.69  thf('4', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ X1))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup+', [status(thm)], ['2', '3'])).
% 2.50/2.69  thf('5', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69             (k1_relat_1 @ X1)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['4'])).
% 2.50/2.69  thf('6', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf('7', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('split', [status(esa)], ['0'])).
% 2.50/2.69  thf(t12_xboole_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.50/2.69  thf('8', plain,
% 2.50/2.69      (![X3 : $i, X4 : $i]:
% 2.50/2.69         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.50/2.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.50/2.69  thf('9', plain,
% 2.50/2.69      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 2.50/2.69          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['7', '8'])).
% 2.50/2.69  thf(t11_xboole_1, axiom,
% 2.50/2.69    (![A:$i,B:$i,C:$i]:
% 2.50/2.69     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.50/2.69  thf('10', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 2.50/2.69      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.50/2.69  thf('11', plain,
% 2.50/2.69      ((![X0 : $i]:
% 2.50/2.69          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 2.50/2.69           | (r1_tarski @ sk_C @ X0)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['9', '10'])).
% 2.50/2.69  thf('12', plain,
% 2.50/2.69      ((![X0 : $i]:
% 2.50/2.69          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 2.50/2.69           | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69           | ~ (v1_relat_1 @ sk_B)
% 2.50/2.69           | (r1_tarski @ sk_C @ X0)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['6', '11'])).
% 2.50/2.69  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('15', plain,
% 2.50/2.69      ((![X0 : $i]:
% 2.50/2.69          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 2.50/2.69           | (r1_tarski @ sk_C @ X0)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.50/2.69  thf('16', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_relat_1 @ sk_B)
% 2.50/2.69         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['5', '15'])).
% 2.50/2.69  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('19', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.50/2.69  thf('20', plain,
% 2.50/2.69      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.50/2.69        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 2.50/2.69        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('21', plain,
% 2.50/2.69      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.50/2.69         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.50/2.69      inference('split', [status(esa)], ['20'])).
% 2.50/2.69  thf('22', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.50/2.69       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['19', '21'])).
% 2.50/2.69  thf('23', plain,
% 2.50/2.69      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.50/2.69       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.50/2.69       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.50/2.69      inference('split', [status(esa)], ['20'])).
% 2.50/2.69  thf('24', plain,
% 2.50/2.69      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.50/2.69        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('25', plain,
% 2.50/2.69      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.50/2.69      inference('split', [status(esa)], ['24'])).
% 2.50/2.69  thf('26', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.50/2.69      inference('split', [status(esa)], ['0'])).
% 2.50/2.69  thf(t163_funct_1, axiom,
% 2.50/2.69    (![A:$i,B:$i,C:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.50/2.69       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 2.50/2.69           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 2.50/2.69         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.50/2.69  thf('27', plain,
% 2.50/2.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.50/2.69         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 2.50/2.69          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 2.50/2.69          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 2.50/2.69          | ~ (v1_funct_1 @ X30)
% 2.50/2.69          | ~ (v1_relat_1 @ X30))),
% 2.50/2.69      inference('cnf', [status(esa)], [t163_funct_1])).
% 2.50/2.69  thf('28', plain,
% 2.50/2.69      ((![X0 : $i]:
% 2.50/2.69          (~ (v1_relat_1 @ sk_A)
% 2.50/2.69           | ~ (v1_funct_1 @ sk_A)
% 2.50/2.69           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 2.50/2.69           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['26', '27'])).
% 2.50/2.69  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('31', plain,
% 2.50/2.69      ((![X0 : $i]:
% 2.50/2.69          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 2.50/2.69           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.50/2.69      inference('demod', [status(thm)], ['28', '29', '30'])).
% 2.50/2.69  thf('32', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 2.50/2.69             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['25', '31'])).
% 2.50/2.69  thf('33', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf('34', plain,
% 2.50/2.69      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.50/2.69         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('split', [status(esa)], ['20'])).
% 2.50/2.69  thf('35', plain,
% 2.50/2.69      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_relat_1 @ sk_B)))
% 2.50/2.69         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['33', '34'])).
% 2.50/2.69  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('38', plain,
% 2.50/2.69      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 2.50/2.69         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.50/2.69  thf('39', plain,
% 2.50/2.69      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.50/2.69       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.50/2.69       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['32', '38'])).
% 2.50/2.69  thf('40', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.50/2.69       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.50/2.69      inference('split', [status(esa)], ['24'])).
% 2.50/2.69  thf(t148_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ B ) =>
% 2.50/2.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.50/2.69  thf('41', plain,
% 2.50/2.69      (![X12 : $i, X13 : $i]:
% 2.50/2.69         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 2.50/2.69          | ~ (v1_relat_1 @ X12))),
% 2.50/2.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.50/2.69  thf(dt_k7_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.50/2.69  thf('42', plain,
% 2.50/2.69      (![X7 : $i, X8 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.50/2.69  thf(t112_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ B ) =>
% 2.50/2.69       ( ![C:$i]:
% 2.50/2.69         ( ( v1_relat_1 @ C ) =>
% 2.50/2.69           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.50/2.69             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 2.50/2.69  thf('43', plain,
% 2.50/2.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X9)
% 2.50/2.69          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 2.50/2.69              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 2.50/2.69          | ~ (v1_relat_1 @ X10))),
% 2.50/2.69      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.50/2.69  thf(dt_k5_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.50/2.69       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.50/2.69  thf('44', plain,
% 2.50/2.69      (![X5 : $i, X6 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X5)
% 2.50/2.69          | ~ (v1_relat_1 @ X6)
% 2.50/2.69          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.50/2.69  thf('45', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('split', [status(esa)], ['0'])).
% 2.50/2.69  thf(t91_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ B ) =>
% 2.50/2.69       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.50/2.69         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.50/2.69  thf('46', plain,
% 2.50/2.69      (![X18 : $i, X19 : $i]:
% 2.50/2.69         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 2.50/2.69          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 2.50/2.69          | ~ (v1_relat_1 @ X19))),
% 2.50/2.69      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.50/2.69  thf('47', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 2.50/2.69         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.50/2.69             = (sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['45', '46'])).
% 2.50/2.69  thf('48', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ sk_B)
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.50/2.69             = (sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['44', '47'])).
% 2.50/2.69  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('51', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.50/2.69          = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['48', '49', '50'])).
% 2.50/2.69  thf('52', plain,
% 2.50/2.69      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 2.50/2.69           = (sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_relat_1 @ sk_B)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['43', '51'])).
% 2.50/2.69  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('55', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 2.50/2.69          = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['52', '53', '54'])).
% 2.50/2.69  thf('56', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf('57', plain,
% 2.50/2.69      (((((sk_C)
% 2.50/2.69           = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_B)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['55', '56'])).
% 2.50/2.69  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('59', plain,
% 2.50/2.69      (((((sk_C)
% 2.50/2.69           = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['57', '58'])).
% 2.50/2.69  thf('60', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ((sk_C)
% 2.50/2.69             = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['42', '59'])).
% 2.50/2.69  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('62', plain,
% 2.50/2.69      ((((sk_C)
% 2.50/2.69          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['60', '61'])).
% 2.50/2.69  thf(t145_funct_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.50/2.69       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.50/2.69  thf('63', plain,
% 2.50/2.69      (![X27 : $i, X28 : $i]:
% 2.50/2.69         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 2.50/2.69          | ~ (v1_funct_1 @ X27)
% 2.50/2.69          | ~ (v1_relat_1 @ X27))),
% 2.50/2.69      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.50/2.69  thf('64', plain,
% 2.50/2.69      ((((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C) @ 
% 2.50/2.69          (k1_relat_1 @ sk_B))
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.50/2.69         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['62', '63'])).
% 2.50/2.69  thf(t94_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ B ) =>
% 2.50/2.69       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.50/2.69  thf('65', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('66', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('67', plain,
% 2.50/2.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X9)
% 2.50/2.69          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 2.50/2.69              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 2.50/2.69          | ~ (v1_relat_1 @ X10))),
% 2.50/2.69      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.50/2.69  thf('68', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.50/2.69            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('sup+', [status(thm)], ['66', '67'])).
% 2.50/2.69  thf(fc3_funct_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.50/2.69       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.50/2.69  thf('69', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('70', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.50/2.69            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['68', '69'])).
% 2.50/2.69  thf('71', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.50/2.69              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['70'])).
% 2.50/2.69  thf('72', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('73', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.50/2.69  thf('74', plain,
% 2.50/2.69      (![X18 : $i, X19 : $i]:
% 2.50/2.69         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 2.50/2.69          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 2.50/2.69          | ~ (v1_relat_1 @ X19))),
% 2.50/2.69      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.50/2.69  thf('75', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['73', '74'])).
% 2.50/2.69  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('77', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['75', '76'])).
% 2.50/2.69  thf('78', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('79', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf('80', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('sup+', [status(thm)], ['78', '79'])).
% 2.50/2.69  thf('81', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('82', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['80', '81'])).
% 2.50/2.69  thf('83', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['82'])).
% 2.50/2.69  thf('84', plain,
% 2.50/2.69      (![X5 : $i, X6 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X5)
% 2.50/2.69          | ~ (v1_relat_1 @ X6)
% 2.50/2.69          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.50/2.69  thf('85', plain,
% 2.50/2.69      (![X14 : $i, X15 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X14)
% 2.50/2.69          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 2.50/2.69              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 2.50/2.69          | ~ (v1_relat_1 @ X15))),
% 2.50/2.69      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.50/2.69  thf(t98_relat_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) =>
% 2.50/2.69       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 2.50/2.69  thf('86', plain,
% 2.50/2.69      (![X22 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 2.50/2.69          | ~ (v1_relat_1 @ X22))),
% 2.50/2.69      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.50/2.69  thf('87', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['82'])).
% 2.50/2.69  thf('88', plain,
% 2.50/2.69      (![X22 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 2.50/2.69          | ~ (v1_relat_1 @ X22))),
% 2.50/2.69      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.50/2.69  thf('89', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['82'])).
% 2.50/2.69  thf('90', plain,
% 2.50/2.69      (![X27 : $i, X28 : $i]:
% 2.50/2.69         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 2.50/2.69          | ~ (v1_funct_1 @ X27)
% 2.50/2.69          | ~ (v1_relat_1 @ X27))),
% 2.50/2.69      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.50/2.69  thf('91', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ 
% 2.50/2.69           (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.50/2.69            (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 2.50/2.69           (k1_relat_1 @ X1))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['89', '90'])).
% 2.50/2.69  thf('92', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('93', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('94', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ 
% 2.50/2.69           (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.50/2.69            (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 2.50/2.69           (k1_relat_1 @ X1))
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.50/2.69  thf('95', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         ((r1_tarski @ 
% 2.50/2.69           (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup+', [status(thm)], ['88', '94'])).
% 2.50/2.69  thf('96', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ 
% 2.50/2.69             (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69             (k1_relat_1 @ X0)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['95'])).
% 2.50/2.69  thf('97', plain,
% 2.50/2.69      (![X22 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 2.50/2.69          | ~ (v1_relat_1 @ X22))),
% 2.50/2.69      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.50/2.69  thf('98', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('99', plain,
% 2.50/2.69      (![X16 : $i, X17 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X16)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 2.50/2.69             (k1_relat_1 @ X17))
% 2.50/2.69          | ~ (v1_relat_1 @ X17))),
% 2.50/2.69      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.50/2.69  thf('100', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('sup+', [status(thm)], ['98', '99'])).
% 2.50/2.69  thf('101', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('102', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k6_relat_1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['100', '101'])).
% 2.50/2.69  thf('103', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69             (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['102'])).
% 2.50/2.69  thf('104', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69           (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup+', [status(thm)], ['97', '103'])).
% 2.50/2.69  thf('105', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69             (k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['104'])).
% 2.50/2.69  thf('106', plain,
% 2.50/2.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.50/2.69         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 2.50/2.69          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 2.50/2.69          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 2.50/2.69          | ~ (v1_funct_1 @ X30)
% 2.50/2.69          | ~ (v1_relat_1 @ X30))),
% 2.50/2.69      inference('cnf', [status(esa)], [t163_funct_1])).
% 2.50/2.69  thf('107', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.50/2.69          | ~ (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 2.50/2.69          | ~ (r1_tarski @ 
% 2.50/2.69               (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69                (k1_relat_1 @ X0)) @ 
% 2.50/2.69               X1))),
% 2.50/2.69      inference('sup-', [status(thm)], ['105', '106'])).
% 2.50/2.69  thf('108', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('109', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('110', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 2.50/2.69          | ~ (r1_tarski @ 
% 2.50/2.69               (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69                (k1_relat_1 @ X0)) @ 
% 2.50/2.69               X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.50/2.69  thf('111', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69              (k1_relat_1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup-', [status(thm)], ['96', '110'])).
% 2.50/2.69  thf('112', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69           (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('simplify', [status(thm)], ['111'])).
% 2.50/2.69  thf('113', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69           (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup+', [status(thm)], ['87', '112'])).
% 2.50/2.69  thf('114', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 2.50/2.69             (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['113'])).
% 2.50/2.69  thf('115', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('sup+', [status(thm)], ['86', '114'])).
% 2.50/2.69  thf('116', plain,
% 2.50/2.69      (![X0 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['115'])).
% 2.50/2.69  thf('117', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['85', '116'])).
% 2.50/2.69  thf('118', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['84', '117'])).
% 2.50/2.69  thf('119', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('simplify', [status(thm)], ['118'])).
% 2.50/2.69  thf('120', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['83', '119'])).
% 2.50/2.69  thf('121', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('122', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['120', '121'])).
% 2.50/2.69  thf('123', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.50/2.69             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.50/2.69      inference('simplify', [status(thm)], ['122'])).
% 2.50/2.69  thf('124', plain,
% 2.50/2.69      ((((r1_tarski @ sk_C @ 
% 2.50/2.69          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['77', '123'])).
% 2.50/2.69  thf('125', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('126', plain,
% 2.50/2.69      (((r1_tarski @ sk_C @ 
% 2.50/2.69         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['124', '125'])).
% 2.50/2.69  thf('127', plain,
% 2.50/2.69      (![X3 : $i, X4 : $i]:
% 2.50/2.69         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.50/2.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.50/2.69  thf('128', plain,
% 2.50/2.69      ((((k2_xboole_0 @ sk_C @ 
% 2.50/2.69          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69          = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['126', '127'])).
% 2.50/2.69  thf('129', plain,
% 2.50/2.69      (((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69           = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['72', '128'])).
% 2.50/2.69  thf('130', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['75', '76'])).
% 2.50/2.69  thf('131', plain,
% 2.50/2.69      (![X7 : $i, X8 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.50/2.69  thf('132', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 2.50/2.69          = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['52', '53', '54'])).
% 2.50/2.69  thf('133', plain,
% 2.50/2.69      (![X16 : $i, X17 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X16)
% 2.50/2.69          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 2.50/2.69             (k1_relat_1 @ X17))
% 2.50/2.69          | ~ (v1_relat_1 @ X17))),
% 2.50/2.69      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.50/2.69  thf('134', plain,
% 2.50/2.69      (![X3 : $i, X4 : $i]:
% 2.50/2.69         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.50/2.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.50/2.69  thf('135', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k2_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 2.50/2.69              (k1_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['133', '134'])).
% 2.50/2.69  thf('136', plain,
% 2.50/2.69      (((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_B)
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['132', '135'])).
% 2.50/2.69  thf('137', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['75', '76'])).
% 2.50/2.69  thf('138', plain,
% 2.50/2.69      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['75', '76'])).
% 2.50/2.69  thf('139', plain, ((v1_relat_1 @ sk_B)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('140', plain,
% 2.50/2.69      (((((k2_xboole_0 @ sk_C @ sk_C) = (sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 2.50/2.69  thf('141', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ sk_A) | ((k2_xboole_0 @ sk_C @ sk_C) = (sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['131', '140'])).
% 2.50/2.69  thf('142', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('143', plain,
% 2.50/2.69      ((((k2_xboole_0 @ sk_C @ sk_C) = (sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['141', '142'])).
% 2.50/2.69  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('145', plain,
% 2.50/2.69      ((((sk_C) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['129', '130', '143', '144'])).
% 2.50/2.69  thf('146', plain,
% 2.50/2.69      (![X5 : $i, X6 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X5)
% 2.50/2.69          | ~ (v1_relat_1 @ X6)
% 2.50/2.69          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.50/2.69  thf('147', plain,
% 2.50/2.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X9)
% 2.50/2.69          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 2.50/2.69              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 2.50/2.69          | ~ (v1_relat_1 @ X10))),
% 2.50/2.69      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.50/2.69  thf('148', plain,
% 2.50/2.69      (![X22 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 2.50/2.69          | ~ (v1_relat_1 @ X22))),
% 2.50/2.69      inference('cnf', [status(esa)], [t98_relat_1])).
% 2.50/2.69  thf('149', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (((k5_relat_1 @ 
% 2.50/2.69            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.50/2.69            = (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['147', '148'])).
% 2.50/2.69  thf('150', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ((k5_relat_1 @ 
% 2.50/2.69              (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.50/2.69              = (k5_relat_1 @ X1 @ X0)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['146', '149'])).
% 2.50/2.69  thf('151', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (((k5_relat_1 @ 
% 2.50/2.69            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.50/2.69            = (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('simplify', [status(thm)], ['150'])).
% 2.50/2.69  thf('152', plain,
% 2.50/2.69      (((((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_C) @ sk_A)
% 2.50/2.69           = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['145', '151'])).
% 2.50/2.69  thf('153', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('154', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('155', plain,
% 2.50/2.69      ((((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_C) @ sk_A)
% 2.50/2.69          = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.50/2.69  thf('156', plain,
% 2.50/2.69      (((((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.50/2.69           = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['71', '155'])).
% 2.50/2.69  thf('157', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('158', plain,
% 2.50/2.69      ((((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.50/2.69          = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['156', '157'])).
% 2.50/2.69  thf('159', plain,
% 2.50/2.69      (![X12 : $i, X13 : $i]:
% 2.50/2.69         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 2.50/2.69          | ~ (v1_relat_1 @ X12))),
% 2.50/2.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.50/2.69  thf('160', plain,
% 2.50/2.69      (((((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69           = (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['158', '159'])).
% 2.50/2.69  thf('161', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('162', plain,
% 2.50/2.69      ((((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_C) @ sk_A)
% 2.50/2.69          = (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.50/2.69  thf('163', plain,
% 2.50/2.69      (![X5 : $i, X6 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X5)
% 2.50/2.69          | ~ (v1_relat_1 @ X6)
% 2.50/2.69          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.50/2.69  thf('164', plain,
% 2.50/2.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X9)
% 2.50/2.69          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 2.50/2.69              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 2.50/2.69          | ~ (v1_relat_1 @ X10))),
% 2.50/2.69      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.50/2.69  thf('165', plain,
% 2.50/2.69      (![X7 : $i, X8 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.50/2.69  thf('166', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X2)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['164', '165'])).
% 2.50/2.69  thf('167', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | (v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['163', '166'])).
% 2.50/2.69  thf('168', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         ((v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('simplify', [status(thm)], ['167'])).
% 2.50/2.69  thf('169', plain,
% 2.50/2.69      ((((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['162', '168'])).
% 2.50/2.69  thf('170', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('171', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('172', plain,
% 2.50/2.69      (((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.50/2.69  thf('173', plain,
% 2.50/2.69      ((((v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['161', '172'])).
% 2.50/2.69  thf('174', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('175', plain,
% 2.50/2.69      (((v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['173', '174'])).
% 2.50/2.69  thf('176', plain,
% 2.50/2.69      ((((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69          = (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['160', '175'])).
% 2.50/2.69  thf('177', plain,
% 2.50/2.69      (((((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.50/2.69           = (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['65', '176'])).
% 2.50/2.69  thf('178', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('179', plain,
% 2.50/2.69      ((((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.50/2.69          = (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['177', '178'])).
% 2.50/2.69  thf('180', plain,
% 2.50/2.69      (((v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['173', '174'])).
% 2.50/2.69  thf('181', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf('182', plain,
% 2.50/2.69      (![X20 : $i, X21 : $i]:
% 2.50/2.69         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 2.50/2.69          | ~ (v1_relat_1 @ X21))),
% 2.50/2.69      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.50/2.69  thf(fc2_funct_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 2.50/2.69         ( v1_funct_1 @ B ) ) =>
% 2.50/2.69       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 2.50/2.69         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 2.50/2.69  thf('183', plain,
% 2.50/2.69      (![X23 : $i, X24 : $i]:
% 2.50/2.69         (~ (v1_funct_1 @ X23)
% 2.50/2.69          | ~ (v1_relat_1 @ X23)
% 2.50/2.69          | ~ (v1_relat_1 @ X24)
% 2.50/2.69          | ~ (v1_funct_1 @ X24)
% 2.50/2.69          | (v1_funct_1 @ (k5_relat_1 @ X23 @ X24)))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 2.50/2.69  thf('184', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_funct_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.50/2.69          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 2.50/2.69      inference('sup+', [status(thm)], ['182', '183'])).
% 2.50/2.69  thf('185', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('186', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('187', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_funct_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('demod', [status(thm)], ['184', '185', '186'])).
% 2.50/2.69  thf('188', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_funct_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['187'])).
% 2.50/2.69  thf('189', plain,
% 2.50/2.69      ((((sk_C) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['129', '130', '143', '144'])).
% 2.50/2.69  thf('190', plain,
% 2.50/2.69      (![X7 : $i, X8 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.50/2.69      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.50/2.69  thf('191', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (((k5_relat_1 @ 
% 2.50/2.69            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 2.50/2.69            = (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0))),
% 2.50/2.69      inference('simplify', [status(thm)], ['150'])).
% 2.50/2.69  thf('192', plain,
% 2.50/2.69      (![X23 : $i, X24 : $i]:
% 2.50/2.69         (~ (v1_funct_1 @ X23)
% 2.50/2.69          | ~ (v1_relat_1 @ X23)
% 2.50/2.69          | ~ (v1_relat_1 @ X24)
% 2.50/2.69          | ~ (v1_funct_1 @ X24)
% 2.50/2.69          | (v1_funct_1 @ (k5_relat_1 @ X23 @ X24)))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc2_funct_1])).
% 2.50/2.69  thf('193', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         ((v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_funct_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ 
% 2.50/2.69               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 2.50/2.69          | ~ (v1_funct_1 @ 
% 2.50/2.69               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['191', '192'])).
% 2.50/2.69  thf('194', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_funct_1 @ 
% 2.50/2.69             (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 2.50/2.69          | ~ (v1_relat_1 @ 
% 2.50/2.69               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 2.50/2.69          | ~ (v1_funct_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.50/2.69      inference('simplify', [status(thm)], ['193'])).
% 2.50/2.69  thf('195', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_relat_1 @ X1)
% 2.50/2.69          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1)
% 2.50/2.69          | ~ (v1_funct_1 @ X0)
% 2.50/2.69          | ~ (v1_funct_1 @ 
% 2.50/2.69               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['190', '194'])).
% 2.50/2.69  thf('196', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (v1_funct_1 @ 
% 2.50/2.69             (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 2.50/2.69          | ~ (v1_funct_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X0)
% 2.50/2.69          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('simplify', [status(thm)], ['195'])).
% 2.50/2.69  thf('197', plain,
% 2.50/2.69      (((~ (v1_funct_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_C))
% 2.50/2.69         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 2.50/2.69         | (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)
% 2.50/2.69         | ~ (v1_funct_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['189', '196'])).
% 2.50/2.69  thf('198', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('199', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('200', plain, ((v1_funct_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('201', plain,
% 2.50/2.69      (((~ (v1_funct_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_C) @ sk_C))
% 2.50/2.69         | (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 2.50/2.69  thf('202', plain,
% 2.50/2.69      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 2.50/2.69         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_C))
% 2.50/2.69         | (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup-', [status(thm)], ['188', '201'])).
% 2.50/2.69  thf('203', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('204', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.50/2.69  thf('205', plain,
% 2.50/2.69      (((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['202', '203', '204'])).
% 2.50/2.69  thf('206', plain,
% 2.50/2.69      ((((v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C)) | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['181', '205'])).
% 2.50/2.69  thf('207', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('208', plain,
% 2.50/2.69      (((v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['206', '207'])).
% 2.50/2.69  thf('209', plain,
% 2.50/2.69      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.50/2.69         (k1_relat_1 @ sk_B)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['64', '179', '180', '208'])).
% 2.50/2.69  thf('210', plain,
% 2.50/2.69      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.50/2.69         | ~ (v1_relat_1 @ sk_A)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('sup+', [status(thm)], ['41', '209'])).
% 2.50/2.69  thf('211', plain, ((v1_relat_1 @ sk_A)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('212', plain,
% 2.50/2.69      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.50/2.69      inference('demod', [status(thm)], ['210', '211'])).
% 2.50/2.69  thf('213', plain,
% 2.50/2.69      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.50/2.69         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.50/2.69      inference('split', [status(esa)], ['20'])).
% 2.50/2.69  thf('214', plain,
% 2.50/2.69      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.50/2.69       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['212', '213'])).
% 2.50/2.69  thf('215', plain, ($false),
% 2.50/2.69      inference('sat_resolution*', [status(thm)],
% 2.50/2.69                ['1', '22', '23', '39', '40', '214'])).
% 2.50/2.69  
% 2.50/2.69  % SZS output end Refutation
% 2.50/2.69  
% 2.55/2.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
