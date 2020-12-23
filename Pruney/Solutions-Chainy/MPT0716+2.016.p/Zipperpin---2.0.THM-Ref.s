%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Votvxs7CSB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:21 EST 2020

% Result     : Theorem 5.18s
% Output     : Refutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 368 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   21
%              Number of atoms          : 1589 (5094 expanded)
%              Number of equality atoms :   42 (  87 expanded)
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X28 @ X27 ) @ X29 )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('42',plain,(
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

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('44',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k1_relat_1 @ X31 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X30 @ X31 ) )
       != ( k1_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('56',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('59',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','61','62','63'])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('67',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('68',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('69',plain,
    ( ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
        = ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
        = ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('76',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('96',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('98',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('101',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['93','108'])).

thf('110',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('111',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_funct_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['92','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','91','117'])).

thf('119',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('123',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','39','40','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Votvxs7CSB
% 0.13/0.38  % Computer   : n024.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 13:55:36 EST 2020
% 0.13/0.39  % CPUTime    : 
% 0.13/0.39  % Running portfolio for 600 s
% 0.13/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.39  % Number of cores: 8
% 0.13/0.39  % Python version: Python 3.6.8
% 0.13/0.39  % Running in FO mode
% 5.18/5.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.18/5.39  % Solved by: fo/fo7.sh
% 5.18/5.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.18/5.39  % done 2584 iterations in 4.899s
% 5.18/5.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.18/5.39  % SZS output start Refutation
% 5.18/5.39  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.18/5.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.18/5.39  thf(sk_A_type, type, sk_A: $i).
% 5.18/5.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.18/5.39  thf(sk_C_type, type, sk_C: $i).
% 5.18/5.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.18/5.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.18/5.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.18/5.39  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.18/5.39  thf(sk_B_type, type, sk_B: $i).
% 5.18/5.39  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.18/5.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.18/5.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.18/5.39  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.18/5.39  thf(t171_funct_1, conjecture,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.18/5.39       ( ![B:$i]:
% 5.18/5.39         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.18/5.39           ( ![C:$i]:
% 5.18/5.39             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 5.18/5.39               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 5.18/5.39                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 5.18/5.39  thf(zf_stmt_0, negated_conjecture,
% 5.18/5.39    (~( ![A:$i]:
% 5.18/5.39        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.18/5.39          ( ![B:$i]:
% 5.18/5.39            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.18/5.39              ( ![C:$i]:
% 5.18/5.39                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 5.18/5.39                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 5.18/5.39                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 5.18/5.39    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 5.18/5.39  thf('0', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 5.18/5.39        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('1', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 5.18/5.39       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 5.18/5.39      inference('split', [status(esa)], ['0'])).
% 5.18/5.39  thf(t182_relat_1, axiom,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ A ) =>
% 5.18/5.39       ( ![B:$i]:
% 5.18/5.39         ( ( v1_relat_1 @ B ) =>
% 5.18/5.39           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.18/5.39             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 5.18/5.39  thf('2', plain,
% 5.18/5.39      (![X14 : $i, X15 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X14)
% 5.18/5.39          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 5.18/5.39              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 5.18/5.39          | ~ (v1_relat_1 @ X15))),
% 5.18/5.39      inference('cnf', [status(esa)], [t182_relat_1])).
% 5.18/5.39  thf(t44_relat_1, axiom,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ A ) =>
% 5.18/5.39       ( ![B:$i]:
% 5.18/5.39         ( ( v1_relat_1 @ B ) =>
% 5.18/5.39           ( r1_tarski @
% 5.18/5.39             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 5.18/5.39  thf('3', plain,
% 5.18/5.39      (![X16 : $i, X17 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X16)
% 5.18/5.39          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 5.18/5.39             (k1_relat_1 @ X17))
% 5.18/5.39          | ~ (v1_relat_1 @ X17))),
% 5.18/5.39      inference('cnf', [status(esa)], [t44_relat_1])).
% 5.18/5.39  thf('4', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i]:
% 5.18/5.39         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.18/5.39           (k1_relat_1 @ X1))
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ X0)
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ X0))),
% 5.18/5.39      inference('sup+', [status(thm)], ['2', '3'])).
% 5.18/5.39  thf('5', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X0)
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 5.18/5.39             (k1_relat_1 @ X1)))),
% 5.18/5.39      inference('simplify', [status(thm)], ['4'])).
% 5.18/5.39  thf('6', plain,
% 5.18/5.39      (![X14 : $i, X15 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X14)
% 5.18/5.39          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 5.18/5.39              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 5.18/5.39          | ~ (v1_relat_1 @ X15))),
% 5.18/5.39      inference('cnf', [status(esa)], [t182_relat_1])).
% 5.18/5.39  thf('7', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('split', [status(esa)], ['0'])).
% 5.18/5.39  thf(t12_xboole_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.18/5.39  thf('8', plain,
% 5.18/5.39      (![X3 : $i, X4 : $i]:
% 5.18/5.39         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 5.18/5.39      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.18/5.39  thf('9', plain,
% 5.18/5.39      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 5.18/5.39          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['7', '8'])).
% 5.18/5.39  thf(t11_xboole_1, axiom,
% 5.18/5.39    (![A:$i,B:$i,C:$i]:
% 5.18/5.39     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.18/5.39  thf('10', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 5.18/5.39      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.18/5.39  thf('11', plain,
% 5.18/5.39      ((![X0 : $i]:
% 5.18/5.39          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 5.18/5.39           | (r1_tarski @ sk_C @ X0)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['9', '10'])).
% 5.18/5.39  thf('12', plain,
% 5.18/5.39      ((![X0 : $i]:
% 5.18/5.39          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 5.18/5.39           | ~ (v1_relat_1 @ sk_A)
% 5.18/5.39           | ~ (v1_relat_1 @ sk_B)
% 5.18/5.39           | (r1_tarski @ sk_C @ X0)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['6', '11'])).
% 5.18/5.39  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('15', plain,
% 5.18/5.39      ((![X0 : $i]:
% 5.18/5.39          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 5.18/5.39           | (r1_tarski @ sk_C @ X0)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['12', '13', '14'])).
% 5.18/5.39  thf('16', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ~ (v1_relat_1 @ sk_B)
% 5.18/5.39         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['5', '15'])).
% 5.18/5.39  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('19', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['16', '17', '18'])).
% 5.18/5.39  thf('20', plain,
% 5.18/5.39      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 5.18/5.39        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 5.18/5.39        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('21', plain,
% 5.18/5.39      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 5.18/5.39         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 5.18/5.39      inference('split', [status(esa)], ['20'])).
% 5.18/5.39  thf('22', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 5.18/5.39       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['19', '21'])).
% 5.18/5.39  thf('23', plain,
% 5.18/5.39      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 5.18/5.39       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 5.18/5.39       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 5.18/5.39      inference('split', [status(esa)], ['20'])).
% 5.18/5.39  thf('24', plain,
% 5.18/5.39      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 5.18/5.39        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('25', plain,
% 5.18/5.39      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 5.18/5.39         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 5.18/5.39      inference('split', [status(esa)], ['24'])).
% 5.18/5.39  thf('26', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 5.18/5.39      inference('split', [status(esa)], ['0'])).
% 5.18/5.39  thf(t163_funct_1, axiom,
% 5.18/5.39    (![A:$i,B:$i,C:$i]:
% 5.18/5.39     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.18/5.39       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 5.18/5.39           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 5.18/5.39         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.18/5.39  thf('27', plain,
% 5.18/5.39      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.18/5.39         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 5.18/5.39          | ~ (r1_tarski @ (k9_relat_1 @ X28 @ X27) @ X29)
% 5.18/5.39          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ X29))
% 5.18/5.39          | ~ (v1_funct_1 @ X28)
% 5.18/5.39          | ~ (v1_relat_1 @ X28))),
% 5.18/5.39      inference('cnf', [status(esa)], [t163_funct_1])).
% 5.18/5.39  thf('28', plain,
% 5.18/5.39      ((![X0 : $i]:
% 5.18/5.39          (~ (v1_relat_1 @ sk_A)
% 5.18/5.39           | ~ (v1_funct_1 @ sk_A)
% 5.18/5.39           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 5.18/5.39           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['26', '27'])).
% 5.18/5.39  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('31', plain,
% 5.18/5.39      ((![X0 : $i]:
% 5.18/5.39          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 5.18/5.39           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 5.18/5.39      inference('demod', [status(thm)], ['28', '29', '30'])).
% 5.18/5.39  thf('32', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 5.18/5.39             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['25', '31'])).
% 5.18/5.39  thf('33', plain,
% 5.18/5.39      (![X14 : $i, X15 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X14)
% 5.18/5.39          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 5.18/5.39              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 5.18/5.39          | ~ (v1_relat_1 @ X15))),
% 5.18/5.39      inference('cnf', [status(esa)], [t182_relat_1])).
% 5.18/5.39  thf('34', plain,
% 5.18/5.39      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 5.18/5.39         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('split', [status(esa)], ['20'])).
% 5.18/5.39  thf('35', plain,
% 5.18/5.39      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 5.18/5.39         | ~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ~ (v1_relat_1 @ sk_B)))
% 5.18/5.39         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['33', '34'])).
% 5.18/5.39  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('38', plain,
% 5.18/5.39      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 5.18/5.39         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['35', '36', '37'])).
% 5.18/5.39  thf('39', plain,
% 5.18/5.39      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 5.18/5.39       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 5.18/5.39       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 5.18/5.39      inference('sup-', [status(thm)], ['32', '38'])).
% 5.18/5.39  thf('40', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 5.18/5.39       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 5.18/5.39      inference('split', [status(esa)], ['24'])).
% 5.18/5.39  thf(t148_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ B ) =>
% 5.18/5.39       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.18/5.39  thf('41', plain,
% 5.18/5.39      (![X12 : $i, X13 : $i]:
% 5.18/5.39         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 5.18/5.39          | ~ (v1_relat_1 @ X12))),
% 5.18/5.39      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.18/5.39  thf(t112_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ B ) =>
% 5.18/5.39       ( ![C:$i]:
% 5.18/5.39         ( ( v1_relat_1 @ C ) =>
% 5.18/5.39           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 5.18/5.39             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 5.18/5.39  thf('42', plain,
% 5.18/5.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X9)
% 5.18/5.39          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 5.18/5.39          | ~ (v1_relat_1 @ X10))),
% 5.18/5.39      inference('cnf', [status(esa)], [t112_relat_1])).
% 5.18/5.39  thf(dt_k5_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 5.18/5.39       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 5.18/5.39  thf('43', plain,
% 5.18/5.39      (![X5 : $i, X6 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X5)
% 5.18/5.39          | ~ (v1_relat_1 @ X6)
% 5.18/5.39          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 5.18/5.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 5.18/5.39  thf('44', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('split', [status(esa)], ['0'])).
% 5.18/5.39  thf(t91_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ B ) =>
% 5.18/5.39       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.18/5.39         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 5.18/5.39  thf('45', plain,
% 5.18/5.39      (![X18 : $i, X19 : $i]:
% 5.18/5.39         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 5.18/5.39          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 5.18/5.39          | ~ (v1_relat_1 @ X19))),
% 5.18/5.39      inference('cnf', [status(esa)], [t91_relat_1])).
% 5.18/5.39  thf('46', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 5.18/5.39         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 5.18/5.39             = (sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['44', '45'])).
% 5.18/5.39  thf('47', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ sk_B)
% 5.18/5.39         | ~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 5.18/5.39             = (sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['43', '46'])).
% 5.18/5.39  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('50', plain,
% 5.18/5.39      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 5.18/5.39          = (sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['47', '48', '49'])).
% 5.18/5.39  thf('51', plain,
% 5.18/5.39      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 5.18/5.39           = (sk_C))
% 5.18/5.39         | ~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ~ (v1_relat_1 @ sk_B)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup+', [status(thm)], ['42', '50'])).
% 5.18/5.39  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('54', plain,
% 5.18/5.39      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 5.18/5.39          = (sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['51', '52', '53'])).
% 5.18/5.39  thf(t27_funct_1, axiom,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.18/5.39       ( ![B:$i]:
% 5.18/5.39         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.18/5.39           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 5.18/5.39             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 5.18/5.39  thf('55', plain,
% 5.18/5.39      (![X30 : $i, X31 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X30)
% 5.18/5.39          | ~ (v1_funct_1 @ X30)
% 5.18/5.39          | (r1_tarski @ (k2_relat_1 @ X30) @ (k1_relat_1 @ X31))
% 5.18/5.39          | ((k1_relat_1 @ (k5_relat_1 @ X30 @ X31)) != (k1_relat_1 @ X30))
% 5.18/5.39          | ~ (v1_funct_1 @ X31)
% 5.18/5.39          | ~ (v1_relat_1 @ X31))),
% 5.18/5.39      inference('cnf', [status(esa)], [t27_funct_1])).
% 5.18/5.39  thf('56', plain,
% 5.18/5.39      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 5.18/5.39         | ~ (v1_relat_1 @ sk_B)
% 5.18/5.39         | ~ (v1_funct_1 @ sk_B)
% 5.18/5.39         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 5.18/5.39            (k1_relat_1 @ sk_B))
% 5.18/5.39         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 5.18/5.39         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['54', '55'])).
% 5.18/5.39  thf('57', plain,
% 5.18/5.39      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['16', '17', '18'])).
% 5.18/5.39  thf('58', plain,
% 5.18/5.39      (![X18 : $i, X19 : $i]:
% 5.18/5.39         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 5.18/5.39          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 5.18/5.39          | ~ (v1_relat_1 @ X19))),
% 5.18/5.39      inference('cnf', [status(esa)], [t91_relat_1])).
% 5.18/5.39  thf('59', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['57', '58'])).
% 5.18/5.39  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('61', plain,
% 5.18/5.39      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['59', '60'])).
% 5.18/5.39  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('64', plain,
% 5.18/5.39      (((((sk_C) != (sk_C))
% 5.18/5.39         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 5.18/5.39            (k1_relat_1 @ sk_B))
% 5.18/5.39         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 5.18/5.39         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['56', '61', '62', '63'])).
% 5.18/5.39  thf('65', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 5.18/5.39         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 5.18/5.39         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 5.18/5.39            (k1_relat_1 @ sk_B))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('simplify', [status(thm)], ['64'])).
% 5.18/5.39  thf(dt_k7_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.18/5.39  thf('66', plain,
% 5.18/5.39      (![X7 : $i, X8 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 5.18/5.39      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.18/5.39  thf('67', plain,
% 5.18/5.39      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['59', '60'])).
% 5.18/5.39  thf(t98_relat_1, axiom,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ A ) =>
% 5.18/5.39       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 5.18/5.39  thf('68', plain,
% 5.18/5.39      (![X22 : $i]:
% 5.18/5.39         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 5.18/5.39          | ~ (v1_relat_1 @ X22))),
% 5.18/5.39      inference('cnf', [status(esa)], [t98_relat_1])).
% 5.18/5.39  thf('69', plain,
% 5.18/5.39      (((((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 5.18/5.39           = (k7_relat_1 @ sk_A @ sk_C))
% 5.18/5.39         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup+', [status(thm)], ['67', '68'])).
% 5.18/5.39  thf('70', plain,
% 5.18/5.39      (((~ (v1_relat_1 @ sk_A)
% 5.18/5.39         | ((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 5.18/5.39             = (k7_relat_1 @ sk_A @ sk_C))))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup-', [status(thm)], ['66', '69'])).
% 5.18/5.39  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('72', plain,
% 5.18/5.39      ((((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 5.18/5.39          = (k7_relat_1 @ sk_A @ sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['70', '71'])).
% 5.18/5.39  thf(t94_relat_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( v1_relat_1 @ B ) =>
% 5.18/5.39       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 5.18/5.39  thf('73', plain,
% 5.18/5.39      (![X20 : $i, X21 : $i]:
% 5.18/5.39         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 5.18/5.39          | ~ (v1_relat_1 @ X21))),
% 5.18/5.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 5.18/5.39  thf('74', plain,
% 5.18/5.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X9)
% 5.18/5.39          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 5.18/5.39          | ~ (v1_relat_1 @ X10))),
% 5.18/5.39      inference('cnf', [status(esa)], [t112_relat_1])).
% 5.18/5.39  thf('75', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 5.18/5.39            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 5.18/5.39          | ~ (v1_relat_1 @ X1))),
% 5.18/5.39      inference('sup+', [status(thm)], ['73', '74'])).
% 5.18/5.39  thf(fc3_funct_1, axiom,
% 5.18/5.39    (![A:$i]:
% 5.18/5.39     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.18/5.39       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.18/5.39  thf('76', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 5.18/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.18/5.39  thf('77', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 5.18/5.39            = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1))
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ X1))),
% 5.18/5.39      inference('demod', [status(thm)], ['75', '76'])).
% 5.18/5.39  thf('78', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X1)
% 5.18/5.39          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 5.18/5.39      inference('simplify', [status(thm)], ['77'])).
% 5.18/5.39  thf('79', plain,
% 5.18/5.39      (![X5 : $i, X6 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X5)
% 5.18/5.39          | ~ (v1_relat_1 @ X6)
% 5.18/5.39          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 5.18/5.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 5.18/5.39  thf('80', plain,
% 5.18/5.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X9)
% 5.18/5.39          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 5.18/5.39          | ~ (v1_relat_1 @ X10))),
% 5.18/5.39      inference('cnf', [status(esa)], [t112_relat_1])).
% 5.18/5.39  thf('81', plain,
% 5.18/5.39      (![X7 : $i, X8 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 5.18/5.39      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.18/5.39  thf('82', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         ((v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.18/5.39          | ~ (v1_relat_1 @ X2)
% 5.18/5.39          | ~ (v1_relat_1 @ X0)
% 5.18/5.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 5.18/5.39      inference('sup+', [status(thm)], ['80', '81'])).
% 5.18/5.39  thf('83', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X0)
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ X0)
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | (v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 5.18/5.39      inference('sup-', [status(thm)], ['79', '82'])).
% 5.18/5.39  thf('84', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         ((v1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 5.18/5.39          | ~ (v1_relat_1 @ X1)
% 5.18/5.39          | ~ (v1_relat_1 @ X0))),
% 5.18/5.39      inference('simplify', [status(thm)], ['83'])).
% 5.18/5.39  thf('85', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.18/5.39          | ~ (v1_relat_1 @ X2)
% 5.18/5.39          | ~ (v1_relat_1 @ X2)
% 5.18/5.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 5.18/5.39      inference('sup+', [status(thm)], ['78', '84'])).
% 5.18/5.39  thf('86', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 5.18/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.18/5.39  thf('87', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.18/5.39          | ~ (v1_relat_1 @ X2)
% 5.18/5.39          | ~ (v1_relat_1 @ X2))),
% 5.18/5.39      inference('demod', [status(thm)], ['85', '86'])).
% 5.18/5.39  thf('88', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X2)
% 5.18/5.39          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 5.18/5.39      inference('simplify', [status(thm)], ['87'])).
% 5.18/5.39  thf('89', plain,
% 5.18/5.39      ((((v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) | ~ (v1_relat_1 @ sk_A)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('sup+', [status(thm)], ['72', '88'])).
% 5.18/5.39  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 5.18/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.18/5.39  thf('91', plain,
% 5.18/5.39      (((v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['89', '90'])).
% 5.18/5.39  thf('92', plain,
% 5.18/5.39      ((((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 5.18/5.39          = (k7_relat_1 @ sk_A @ sk_C)))
% 5.18/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.18/5.39      inference('demod', [status(thm)], ['70', '71'])).
% 5.18/5.39  thf('93', plain,
% 5.18/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X1)
% 5.18/5.39          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)))),
% 5.18/5.39      inference('simplify', [status(thm)], ['77'])).
% 5.18/5.39  thf(fc2_funct_1, axiom,
% 5.18/5.39    (![A:$i,B:$i]:
% 5.18/5.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 5.18/5.39         ( v1_funct_1 @ B ) ) =>
% 5.18/5.39       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 5.18/5.39         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 5.18/5.39  thf('94', plain,
% 5.18/5.39      (![X23 : $i, X24 : $i]:
% 5.18/5.39         (~ (v1_funct_1 @ X23)
% 5.18/5.39          | ~ (v1_relat_1 @ X23)
% 5.18/5.39          | ~ (v1_relat_1 @ X24)
% 5.18/5.39          | ~ (v1_funct_1 @ X24)
% 5.18/5.39          | (v1_funct_1 @ (k5_relat_1 @ X23 @ X24)))),
% 5.18/5.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 5.18/5.39  thf('95', plain,
% 5.18/5.39      (![X5 : $i, X6 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X5)
% 5.18/5.39          | ~ (v1_relat_1 @ X6)
% 5.18/5.39          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 5.18/5.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 5.18/5.39  thf('96', plain,
% 5.18/5.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.18/5.39         (~ (v1_relat_1 @ X9)
% 5.18/5.39          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 5.18/5.39              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 5.18/5.39          | ~ (v1_relat_1 @ X10))),
% 5.18/5.39      inference('cnf', [status(esa)], [t112_relat_1])).
% 5.18/5.39  thf('97', plain,
% 5.18/5.39      (![X20 : $i, X21 : $i]:
% 5.18/5.39         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 5.18/5.39          | ~ (v1_relat_1 @ X21))),
% 5.18/5.39      inference('cnf', [status(esa)], [t94_relat_1])).
% 5.18/5.39  thf('98', plain,
% 5.18/5.39      (![X23 : $i, X24 : $i]:
% 5.18/5.39         (~ (v1_funct_1 @ X23)
% 5.18/5.39          | ~ (v1_relat_1 @ X23)
% 5.18/5.39          | ~ (v1_relat_1 @ X24)
% 5.18/5.39          | ~ (v1_funct_1 @ X24)
% 5.18/5.39          | (v1_funct_1 @ (k5_relat_1 @ X23 @ X24)))),
% 5.22/5.39      inference('cnf', [status(esa)], [fc2_funct_1])).
% 5.22/5.39  thf('99', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_funct_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 5.22/5.39          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 5.22/5.39      inference('sup+', [status(thm)], ['97', '98'])).
% 5.22/5.39  thf('100', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 5.22/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.22/5.39  thf('101', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 5.22/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.22/5.39  thf('102', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_funct_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X1))),
% 5.22/5.39      inference('demod', [status(thm)], ['99', '100', '101'])).
% 5.22/5.39  thf('103', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i]:
% 5.22/5.39         (~ (v1_funct_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.22/5.39      inference('simplify', [status(thm)], ['102'])).
% 5.22/5.39  thf('104', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X2)
% 5.22/5.39          | ~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0))
% 5.22/5.39          | ~ (v1_funct_1 @ (k5_relat_1 @ X2 @ X0)))),
% 5.22/5.39      inference('sup+', [status(thm)], ['96', '103'])).
% 5.22/5.39  thf('105', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         (~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | (v1_funct_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 5.22/5.39      inference('sup-', [status(thm)], ['95', '104'])).
% 5.22/5.39  thf('106', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 5.22/5.39          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X0))),
% 5.22/5.39      inference('simplify', [status(thm)], ['105'])).
% 5.22/5.39  thf('107', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         (~ (v1_funct_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_funct_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | (v1_funct_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 5.22/5.39      inference('sup-', [status(thm)], ['94', '106'])).
% 5.22/5.39  thf('108', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 5.22/5.39          | ~ (v1_funct_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X1)
% 5.22/5.39          | ~ (v1_relat_1 @ X0)
% 5.22/5.39          | ~ (v1_funct_1 @ X0))),
% 5.22/5.39      inference('simplify', [status(thm)], ['107'])).
% 5.22/5.39  thf('109', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X2)
% 5.22/5.39          | ~ (v1_funct_1 @ X2)
% 5.22/5.39          | ~ (v1_relat_1 @ X2)
% 5.22/5.39          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 5.22/5.39          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 5.22/5.39      inference('sup+', [status(thm)], ['93', '108'])).
% 5.22/5.39  thf('110', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 5.22/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.22/5.39  thf('111', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 5.22/5.39      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.22/5.39  thf('112', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         ((v1_funct_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 5.22/5.39          | ~ (v1_relat_1 @ X2)
% 5.22/5.39          | ~ (v1_funct_1 @ X2)
% 5.22/5.39          | ~ (v1_relat_1 @ X2))),
% 5.22/5.39      inference('demod', [status(thm)], ['109', '110', '111'])).
% 5.22/5.39  thf('113', plain,
% 5.22/5.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.22/5.39         (~ (v1_funct_1 @ X2)
% 5.22/5.39          | ~ (v1_relat_1 @ X2)
% 5.22/5.39          | (v1_funct_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 5.22/5.39      inference('simplify', [status(thm)], ['112'])).
% 5.22/5.39  thf('114', plain,
% 5.22/5.39      ((((v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 5.22/5.39         | ~ (v1_relat_1 @ sk_A)
% 5.22/5.39         | ~ (v1_funct_1 @ sk_A)))
% 5.22/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.22/5.39      inference('sup+', [status(thm)], ['92', '113'])).
% 5.22/5.39  thf('115', plain, ((v1_relat_1 @ sk_A)),
% 5.22/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.22/5.39  thf('116', plain, ((v1_funct_1 @ sk_A)),
% 5.22/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.22/5.39  thf('117', plain,
% 5.22/5.39      (((v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 5.22/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.22/5.39      inference('demod', [status(thm)], ['114', '115', '116'])).
% 5.22/5.39  thf('118', plain,
% 5.22/5.39      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 5.22/5.39         (k1_relat_1 @ sk_B)))
% 5.22/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.22/5.39      inference('demod', [status(thm)], ['65', '91', '117'])).
% 5.22/5.39  thf('119', plain,
% 5.22/5.39      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 5.22/5.39         | ~ (v1_relat_1 @ sk_A)))
% 5.22/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.22/5.39      inference('sup+', [status(thm)], ['41', '118'])).
% 5.22/5.39  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 5.22/5.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.22/5.39  thf('121', plain,
% 5.22/5.39      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 5.22/5.39         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 5.22/5.39      inference('demod', [status(thm)], ['119', '120'])).
% 5.22/5.39  thf('122', plain,
% 5.22/5.39      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 5.22/5.39         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 5.22/5.39      inference('split', [status(esa)], ['20'])).
% 5.22/5.39  thf('123', plain,
% 5.22/5.39      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 5.22/5.39       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 5.22/5.39      inference('sup-', [status(thm)], ['121', '122'])).
% 5.22/5.39  thf('124', plain, ($false),
% 5.22/5.39      inference('sat_resolution*', [status(thm)],
% 5.22/5.39                ['1', '22', '23', '39', '40', '123'])).
% 5.22/5.39  
% 5.22/5.39  % SZS output end Refutation
% 5.22/5.39  
% 5.22/5.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
