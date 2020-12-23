%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKhXxsAArm

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 520 expanded)
%              Number of leaves         :   30 ( 159 expanded)
%              Depth                    :   41
%              Number of atoms          : 2254 (7339 expanded)
%              Number of equality atoms :   72 ( 145 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('55',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('65',plain,
    ( ( ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( sk_C
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_C
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('72',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('77',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('79',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('98',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X30 @ X29 ) @ X31 )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ X2 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','104'])).

thf('106',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('107',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','115'])).

thf('117',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('124',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','124'])).

thf('126',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('127',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('128',plain,
    ( ( sk_C
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_xboole_0 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['128','131'])).

thf('133',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('134',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('135',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( ( k2_xboole_0 @ sk_C @ sk_C )
        = sk_C )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf('137',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k2_xboole_0 @ sk_C @ sk_C )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_xboole_0 @ sk_C @ sk_C )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( sk_C
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['125','126','139','140'])).

thf('142',plain,
    ( ( ( sk_C
        = ( k10_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','141'])).

thf('143',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( sk_C
      = ( k10_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('147',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k10_relat_1 @ X16 @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('148',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
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
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) @ sk_C )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
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
    ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
        = ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','161'])).

thf('163',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('174',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','39','40','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dKhXxsAArm
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:41:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.42/2.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.42/2.62  % Solved by: fo/fo7.sh
% 2.42/2.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.62  % done 1598 iterations in 2.176s
% 2.42/2.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.42/2.62  % SZS output start Refutation
% 2.42/2.62  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.42/2.62  thf(sk_C_type, type, sk_C: $i).
% 2.42/2.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.42/2.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.42/2.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.42/2.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.42/2.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.42/2.62  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.42/2.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.42/2.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.42/2.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.62  thf(t171_funct_1, conjecture,
% 2.42/2.62    (![A:$i]:
% 2.42/2.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.42/2.62       ( ![B:$i]:
% 2.42/2.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.62           ( ![C:$i]:
% 2.42/2.62             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 2.42/2.62               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 2.42/2.62                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 2.42/2.62  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.62    (~( ![A:$i]:
% 2.42/2.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.42/2.62          ( ![B:$i]:
% 2.42/2.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.62              ( ![C:$i]:
% 2.42/2.62                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 2.42/2.62                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 2.42/2.62                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 2.42/2.62    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 2.42/2.62  thf('0', plain,
% 2.42/2.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 2.42/2.62        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.42/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.62  thf('1', plain,
% 2.42/2.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.42/2.62       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.42/2.62      inference('split', [status(esa)], ['0'])).
% 2.42/2.62  thf(t182_relat_1, axiom,
% 2.42/2.62    (![A:$i]:
% 2.42/2.62     ( ( v1_relat_1 @ A ) =>
% 2.42/2.62       ( ![B:$i]:
% 2.42/2.62         ( ( v1_relat_1 @ B ) =>
% 2.42/2.62           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.42/2.62             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.42/2.62  thf('2', plain,
% 2.42/2.62      (![X15 : $i, X16 : $i]:
% 2.42/2.62         (~ (v1_relat_1 @ X15)
% 2.42/2.62          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.62              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.62          | ~ (v1_relat_1 @ X16))),
% 2.42/2.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.62  thf(t44_relat_1, axiom,
% 2.42/2.62    (![A:$i]:
% 2.42/2.62     ( ( v1_relat_1 @ A ) =>
% 2.42/2.62       ( ![B:$i]:
% 2.42/2.62         ( ( v1_relat_1 @ B ) =>
% 2.42/2.62           ( r1_tarski @
% 2.42/2.62             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 2.42/2.62  thf('3', plain,
% 2.42/2.62      (![X17 : $i, X18 : $i]:
% 2.42/2.62         (~ (v1_relat_1 @ X17)
% 2.42/2.62          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 2.42/2.62             (k1_relat_1 @ X18))
% 2.42/2.62          | ~ (v1_relat_1 @ X18))),
% 2.42/2.62      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.42/2.62  thf('4', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.42/2.62           (k1_relat_1 @ X1))
% 2.42/2.62          | ~ (v1_relat_1 @ X1)
% 2.42/2.62          | ~ (v1_relat_1 @ X0)
% 2.42/2.62          | ~ (v1_relat_1 @ X1)
% 2.42/2.62          | ~ (v1_relat_1 @ X0))),
% 2.42/2.62      inference('sup+', [status(thm)], ['2', '3'])).
% 2.42/2.62  thf('5', plain,
% 2.42/2.62      (![X0 : $i, X1 : $i]:
% 2.42/2.62         (~ (v1_relat_1 @ X0)
% 2.42/2.62          | ~ (v1_relat_1 @ X1)
% 2.42/2.62          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.42/2.62             (k1_relat_1 @ X1)))),
% 2.42/2.62      inference('simplify', [status(thm)], ['4'])).
% 2.42/2.62  thf('6', plain,
% 2.42/2.62      (![X15 : $i, X16 : $i]:
% 2.42/2.62         (~ (v1_relat_1 @ X15)
% 2.42/2.62          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.62              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.62          | ~ (v1_relat_1 @ X16))),
% 2.42/2.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.62  thf('7', plain,
% 2.42/2.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('split', [status(esa)], ['0'])).
% 2.42/2.63  thf(t12_xboole_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.42/2.63  thf('8', plain,
% 2.42/2.63      (![X3 : $i, X4 : $i]:
% 2.42/2.63         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.42/2.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.63  thf('9', plain,
% 2.42/2.63      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 2.42/2.63          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['7', '8'])).
% 2.42/2.63  thf(t11_xboole_1, axiom,
% 2.42/2.63    (![A:$i,B:$i,C:$i]:
% 2.42/2.63     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.42/2.63  thf('10', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.63         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 2.42/2.63      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.42/2.63  thf('11', plain,
% 2.42/2.63      ((![X0 : $i]:
% 2.42/2.63          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 2.42/2.63           | (r1_tarski @ sk_C @ X0)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['9', '10'])).
% 2.42/2.63  thf('12', plain,
% 2.42/2.63      ((![X0 : $i]:
% 2.42/2.63          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 2.42/2.63           | ~ (v1_relat_1 @ sk_A)
% 2.42/2.63           | ~ (v1_relat_1 @ sk_B)
% 2.42/2.63           | (r1_tarski @ sk_C @ X0)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['6', '11'])).
% 2.42/2.63  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('15', plain,
% 2.42/2.63      ((![X0 : $i]:
% 2.42/2.63          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 2.42/2.63           | (r1_tarski @ sk_C @ X0)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 2.42/2.63  thf('16', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_relat_1 @ sk_B)
% 2.42/2.63         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['5', '15'])).
% 2.42/2.63  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('19', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.42/2.63  thf('20', plain,
% 2.42/2.63      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.42/2.63        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 2.42/2.63        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('21', plain,
% 2.42/2.63      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.42/2.63         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.42/2.63      inference('split', [status(esa)], ['20'])).
% 2.42/2.63  thf('22', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.42/2.63       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['19', '21'])).
% 2.42/2.63  thf('23', plain,
% 2.42/2.63      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.42/2.63       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.42/2.63       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.42/2.63      inference('split', [status(esa)], ['20'])).
% 2.42/2.63  thf('24', plain,
% 2.42/2.63      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.42/2.63        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('25', plain,
% 2.42/2.63      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.42/2.63      inference('split', [status(esa)], ['24'])).
% 2.42/2.63  thf('26', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.42/2.63      inference('split', [status(esa)], ['0'])).
% 2.42/2.63  thf(t163_funct_1, axiom,
% 2.42/2.63    (![A:$i,B:$i,C:$i]:
% 2.42/2.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.42/2.63       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 2.42/2.63           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 2.42/2.63         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.42/2.63  thf('27', plain,
% 2.42/2.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.42/2.63         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 2.42/2.63          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 2.42/2.63          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 2.42/2.63          | ~ (v1_funct_1 @ X30)
% 2.42/2.63          | ~ (v1_relat_1 @ X30))),
% 2.42/2.63      inference('cnf', [status(esa)], [t163_funct_1])).
% 2.42/2.63  thf('28', plain,
% 2.42/2.63      ((![X0 : $i]:
% 2.42/2.63          (~ (v1_relat_1 @ sk_A)
% 2.42/2.63           | ~ (v1_funct_1 @ sk_A)
% 2.42/2.63           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 2.42/2.63           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['26', '27'])).
% 2.42/2.63  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('31', plain,
% 2.42/2.63      ((![X0 : $i]:
% 2.42/2.63          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 2.42/2.63           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 2.42/2.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 2.42/2.63  thf('32', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 2.42/2.63             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['25', '31'])).
% 2.42/2.63  thf('33', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf('34', plain,
% 2.42/2.63      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.42/2.63         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('split', [status(esa)], ['20'])).
% 2.42/2.63  thf('35', plain,
% 2.42/2.63      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_relat_1 @ sk_B)))
% 2.42/2.63         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['33', '34'])).
% 2.42/2.63  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('38', plain,
% 2.42/2.63      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.42/2.63  thf('39', plain,
% 2.42/2.63      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 2.42/2.63       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.42/2.63       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.42/2.63      inference('sup-', [status(thm)], ['32', '38'])).
% 2.42/2.63  thf('40', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.42/2.63       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.42/2.63      inference('split', [status(esa)], ['24'])).
% 2.42/2.63  thf(t148_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ B ) =>
% 2.42/2.63       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.42/2.63  thf('41', plain,
% 2.42/2.63      (![X13 : $i, X14 : $i]:
% 2.42/2.63         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 2.42/2.63          | ~ (v1_relat_1 @ X13))),
% 2.42/2.63      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.42/2.63  thf(t94_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ B ) =>
% 2.42/2.63       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.42/2.63  thf('42', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf(fc2_funct_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 2.42/2.63         ( v1_funct_1 @ B ) ) =>
% 2.42/2.63       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 2.42/2.63         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 2.42/2.63  thf('43', plain,
% 2.42/2.63      (![X23 : $i, X24 : $i]:
% 2.42/2.63         (~ (v1_funct_1 @ X23)
% 2.42/2.63          | ~ (v1_relat_1 @ X23)
% 2.42/2.63          | ~ (v1_relat_1 @ X24)
% 2.42/2.63          | ~ (v1_funct_1 @ X24)
% 2.42/2.63          | (v1_funct_1 @ (k5_relat_1 @ X23 @ X24)))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc2_funct_1])).
% 2.42/2.63  thf('44', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.42/2.63          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 2.42/2.63      inference('sup+', [status(thm)], ['42', '43'])).
% 2.42/2.63  thf(fc3_funct_1, axiom,
% 2.42/2.63    (![A:$i]:
% 2.42/2.63     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.42/2.63       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.42/2.63  thf('45', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('46', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('47', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('demod', [status(thm)], ['44', '45', '46'])).
% 2.42/2.63  thf('48', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.42/2.63      inference('simplify', [status(thm)], ['47'])).
% 2.42/2.63  thf(dt_k7_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.42/2.63  thf('49', plain,
% 2.42/2.63      (![X7 : $i, X8 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.42/2.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.63  thf('50', plain,
% 2.42/2.63      (![X7 : $i, X8 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.42/2.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.63  thf(t112_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ B ) =>
% 2.42/2.63       ( ![C:$i]:
% 2.42/2.63         ( ( v1_relat_1 @ C ) =>
% 2.42/2.63           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.42/2.63             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 2.42/2.63  thf('51', plain,
% 2.42/2.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X9)
% 2.42/2.63          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 2.42/2.63              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 2.42/2.63          | ~ (v1_relat_1 @ X10))),
% 2.42/2.63      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.42/2.63  thf(dt_k5_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 2.42/2.63       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 2.42/2.63  thf('52', plain,
% 2.42/2.63      (![X5 : $i, X6 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X5)
% 2.42/2.63          | ~ (v1_relat_1 @ X6)
% 2.42/2.63          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.42/2.63      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.42/2.63  thf('53', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('split', [status(esa)], ['0'])).
% 2.42/2.63  thf(t91_relat_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ B ) =>
% 2.42/2.63       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 2.42/2.63         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.42/2.63  thf('54', plain,
% 2.42/2.63      (![X19 : $i, X20 : $i]:
% 2.42/2.63         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 2.42/2.63          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 2.42/2.63          | ~ (v1_relat_1 @ X20))),
% 2.42/2.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.42/2.63  thf('55', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 2.42/2.63         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.42/2.63             = (sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['53', '54'])).
% 2.42/2.63  thf('56', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_B)
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.42/2.63             = (sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['52', '55'])).
% 2.42/2.63  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('59', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.42/2.63          = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 2.42/2.63  thf('60', plain,
% 2.42/2.63      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 2.42/2.63           = (sk_C))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_relat_1 @ sk_B)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['51', '59'])).
% 2.42/2.63  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('63', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 2.42/2.63          = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.42/2.63  thf('64', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf('65', plain,
% 2.42/2.63      (((((sk_C)
% 2.42/2.63           = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_B)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['63', '64'])).
% 2.42/2.63  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('67', plain,
% 2.42/2.63      (((((sk_C)
% 2.42/2.63           = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['65', '66'])).
% 2.42/2.63  thf('68', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ((sk_C)
% 2.42/2.63             = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['50', '67'])).
% 2.42/2.63  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('70', plain,
% 2.42/2.63      ((((sk_C)
% 2.42/2.63          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['68', '69'])).
% 2.42/2.63  thf(t145_funct_1, axiom,
% 2.42/2.63    (![A:$i,B:$i]:
% 2.42/2.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.42/2.63       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.42/2.63  thf('71', plain,
% 2.42/2.63      (![X27 : $i, X28 : $i]:
% 2.42/2.63         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 2.42/2.63          | ~ (v1_funct_1 @ X27)
% 2.42/2.63          | ~ (v1_relat_1 @ X27))),
% 2.42/2.63      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.42/2.63  thf('72', plain,
% 2.42/2.63      ((((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C) @ 
% 2.42/2.63          (k1_relat_1 @ sk_B))
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.42/2.63         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['70', '71'])).
% 2.42/2.63  thf('73', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('74', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('75', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf('76', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('77', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.42/2.63  thf('78', plain,
% 2.42/2.63      (![X19 : $i, X20 : $i]:
% 2.42/2.63         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 2.42/2.63          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 2.42/2.63          | ~ (v1_relat_1 @ X20))),
% 2.42/2.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.42/2.63  thf('79', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['77', '78'])).
% 2.42/2.63  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('81', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['79', '80'])).
% 2.42/2.63  thf('82', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('83', plain,
% 2.42/2.63      (![X17 : $i, X18 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X17)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 2.42/2.63             (k1_relat_1 @ X18))
% 2.42/2.63          | ~ (v1_relat_1 @ X18))),
% 2.42/2.63      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.42/2.63  thf('84', plain,
% 2.42/2.63      (![X19 : $i, X20 : $i]:
% 2.42/2.63         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 2.42/2.63          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 2.42/2.63          | ~ (v1_relat_1 @ X20))),
% 2.42/2.63      inference('cnf', [status(esa)], [t91_relat_1])).
% 2.42/2.63  thf('85', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ((k1_relat_1 @ 
% 2.42/2.63              (k7_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))
% 2.42/2.63              = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['83', '84'])).
% 2.42/2.63  thf('86', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k1_relat_1 @ 
% 2.42/2.63            (k7_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))
% 2.42/2.63            = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0))),
% 2.42/2.63      inference('simplify', [status(thm)], ['85'])).
% 2.42/2.63  thf('87', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k1_relat_1 @ 
% 2.42/2.63            (k7_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))
% 2.42/2.63            = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0))),
% 2.42/2.63      inference('simplify', [status(thm)], ['85'])).
% 2.42/2.63  thf('88', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('89', plain,
% 2.42/2.63      (![X21 : $i, X22 : $i]:
% 2.42/2.63         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 2.42/2.63          | ~ (v1_relat_1 @ X22))),
% 2.42/2.63      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.42/2.63  thf('90', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf('91', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.42/2.63            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('sup+', [status(thm)], ['89', '90'])).
% 2.42/2.63  thf('92', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('93', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.42/2.63            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('demod', [status(thm)], ['91', '92'])).
% 2.42/2.63  thf('94', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X1)
% 2.42/2.63          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.42/2.63              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['93'])).
% 2.42/2.63  thf('95', plain,
% 2.42/2.63      (![X27 : $i, X28 : $i]:
% 2.42/2.63         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 2.42/2.63          | ~ (v1_funct_1 @ X27)
% 2.42/2.63          | ~ (v1_relat_1 @ X27))),
% 2.42/2.63      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.42/2.63  thf('96', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf('97', plain,
% 2.42/2.63      (![X17 : $i, X18 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X17)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 2.42/2.63             (k1_relat_1 @ X18))
% 2.42/2.63          | ~ (v1_relat_1 @ X18))),
% 2.42/2.63      inference('cnf', [status(esa)], [t44_relat_1])).
% 2.42/2.63  thf('98', plain,
% 2.42/2.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.42/2.63         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 2.42/2.63          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 2.42/2.63          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 2.42/2.63          | ~ (v1_funct_1 @ X30)
% 2.42/2.63          | ~ (v1_relat_1 @ X30))),
% 2.42/2.63      inference('cnf', [status(esa)], [t163_funct_1])).
% 2.42/2.63  thf('99', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_funct_1 @ X0)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 2.42/2.63             (k10_relat_1 @ X0 @ X2))
% 2.42/2.63          | ~ (r1_tarski @ 
% 2.42/2.63               (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))) @ X2))),
% 2.42/2.63      inference('sup-', [status(thm)], ['97', '98'])).
% 2.42/2.63  thf('100', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.63         (~ (r1_tarski @ 
% 2.42/2.63             (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))) @ X2)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 2.42/2.63             (k10_relat_1 @ X0 @ X2))
% 2.42/2.63          | ~ (v1_funct_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0))),
% 2.42/2.63      inference('simplify', [status(thm)], ['99'])).
% 2.42/2.63  thf('101', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.63         (~ (r1_tarski @ 
% 2.42/2.63             (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ X2)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k10_relat_1 @ X1 @ X2)))),
% 2.42/2.63      inference('sup-', [status(thm)], ['96', '100'])).
% 2.42/2.63  thf('102', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k10_relat_1 @ X1 @ X2))
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (r1_tarski @ 
% 2.42/2.63               (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ X2))),
% 2.42/2.63      inference('simplify', [status(thm)], ['101'])).
% 2.42/2.63  thf('103', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['95', '102'])).
% 2.42/2.63  thf('104', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_funct_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('simplify', [status(thm)], ['103'])).
% 2.42/2.63  thf('105', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 2.42/2.63           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.42/2.63          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('sup+', [status(thm)], ['94', '104'])).
% 2.42/2.63  thf('106', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('107', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('108', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 2.42/2.63           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('demod', [status(thm)], ['105', '106', '107'])).
% 2.42/2.63  thf('109', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ 
% 2.42/2.63             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 2.42/2.63             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['108'])).
% 2.42/2.63  thf('110', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('sup+', [status(thm)], ['88', '109'])).
% 2.42/2.63  thf('111', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['110'])).
% 2.42/2.63  thf('112', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k1_relat_1 @ 
% 2.42/2.63            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('sup+', [status(thm)], ['87', '111'])).
% 2.42/2.63  thf('113', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k1_relat_1 @ 
% 2.42/2.63              (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['112'])).
% 2.42/2.63  thf('114', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0))),
% 2.42/2.63      inference('sup+', [status(thm)], ['86', '113'])).
% 2.42/2.63  thf('115', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['114'])).
% 2.42/2.63  thf('116', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('sup+', [status(thm)], ['82', '115'])).
% 2.42/2.63  thf('117', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('118', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63           (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X1))),
% 2.42/2.63      inference('demod', [status(thm)], ['116', '117'])).
% 2.42/2.63  thf('119', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 2.42/2.63             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.42/2.63      inference('simplify', [status(thm)], ['118'])).
% 2.42/2.63  thf('120', plain,
% 2.42/2.63      ((((r1_tarski @ sk_C @ 
% 2.42/2.63          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['81', '119'])).
% 2.42/2.63  thf('121', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('122', plain,
% 2.42/2.63      (((r1_tarski @ sk_C @ 
% 2.42/2.63         (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['120', '121'])).
% 2.42/2.63  thf('123', plain,
% 2.42/2.63      (![X3 : $i, X4 : $i]:
% 2.42/2.63         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.42/2.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.63  thf('124', plain,
% 2.42/2.63      ((((k2_xboole_0 @ sk_C @ 
% 2.42/2.63          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.42/2.63          = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['122', '123'])).
% 2.42/2.63  thf('125', plain,
% 2.42/2.63      (((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.42/2.63           = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['76', '124'])).
% 2.42/2.63  thf('126', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['79', '80'])).
% 2.42/2.63  thf('127', plain,
% 2.42/2.63      (![X7 : $i, X8 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 2.42/2.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.42/2.63  thf('128', plain,
% 2.42/2.63      ((((sk_C)
% 2.42/2.63          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['68', '69'])).
% 2.42/2.63  thf('129', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.42/2.63             (k1_relat_1 @ X1)))),
% 2.42/2.63      inference('simplify', [status(thm)], ['4'])).
% 2.42/2.63  thf('130', plain,
% 2.42/2.63      (![X3 : $i, X4 : $i]:
% 2.42/2.63         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 2.42/2.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.42/2.63  thf('131', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ((k2_xboole_0 @ (k10_relat_1 @ X0 @ (k1_relat_1 @ X1)) @ 
% 2.42/2.63              (k1_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 2.42/2.63      inference('sup-', [status(thm)], ['129', '130'])).
% 2.42/2.63  thf('132', plain,
% 2.42/2.63      (((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.42/2.63           = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_B)
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['128', '131'])).
% 2.42/2.63  thf('133', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['79', '80'])).
% 2.42/2.63  thf('134', plain,
% 2.42/2.63      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['79', '80'])).
% 2.42/2.63  thf('135', plain, ((v1_relat_1 @ sk_B)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('136', plain,
% 2.42/2.63      (((((k2_xboole_0 @ sk_C @ sk_C) = (sk_C))
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 2.42/2.63  thf('137', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A) | ((k2_xboole_0 @ sk_C @ sk_C) = (sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['127', '136'])).
% 2.42/2.63  thf('138', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('139', plain,
% 2.42/2.63      ((((k2_xboole_0 @ sk_C @ sk_C) = (sk_C)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['137', '138'])).
% 2.42/2.63  thf('140', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('141', plain,
% 2.42/2.63      ((((sk_C) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['125', '126', '139', '140'])).
% 2.42/2.63  thf('142', plain,
% 2.42/2.63      (((((sk_C) = (k10_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_A)))
% 2.42/2.63         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['75', '141'])).
% 2.42/2.63  thf('143', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('145', plain,
% 2.42/2.63      ((((sk_C) = (k10_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['142', '143', '144'])).
% 2.42/2.63  thf('146', plain,
% 2.42/2.63      (![X5 : $i, X6 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X5)
% 2.42/2.63          | ~ (v1_relat_1 @ X6)
% 2.42/2.63          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 2.42/2.63      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 2.42/2.63  thf('147', plain,
% 2.42/2.63      (![X15 : $i, X16 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X15)
% 2.42/2.63          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.42/2.63              = (k10_relat_1 @ X16 @ (k1_relat_1 @ X15)))
% 2.42/2.63          | ~ (v1_relat_1 @ X16))),
% 2.42/2.63      inference('cnf', [status(esa)], [t182_relat_1])).
% 2.42/2.63  thf(t146_relat_1, axiom,
% 2.42/2.63    (![A:$i]:
% 2.42/2.63     ( ( v1_relat_1 @ A ) =>
% 2.42/2.63       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.42/2.63  thf('148', plain,
% 2.42/2.63      (![X12 : $i]:
% 2.42/2.63         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 2.42/2.63          | ~ (v1_relat_1 @ X12))),
% 2.42/2.63      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.42/2.63  thf('149', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.42/2.63            (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.42/2.63            = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 2.42/2.63      inference('sup+', [status(thm)], ['147', '148'])).
% 2.42/2.63  thf('150', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0)
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ((k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.42/2.63              (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.42/2.63              = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['146', '149'])).
% 2.42/2.63  thf('151', plain,
% 2.42/2.63      (![X0 : $i, X1 : $i]:
% 2.42/2.63         (((k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 2.42/2.63            (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 2.42/2.63            = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.42/2.63          | ~ (v1_relat_1 @ X1)
% 2.42/2.63          | ~ (v1_relat_1 @ X0))),
% 2.42/2.63      inference('simplify', [status(thm)], ['150'])).
% 2.42/2.63  thf('152', plain,
% 2.42/2.63      (((((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A) @ sk_C)
% 2.42/2.63           = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['145', '151'])).
% 2.42/2.63  thf('153', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('154', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 2.42/2.63      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.42/2.63  thf('155', plain,
% 2.42/2.63      ((((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A) @ sk_C)
% 2.42/2.63          = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.42/2.63  thf('156', plain,
% 2.42/2.63      (((((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.42/2.63           = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['74', '155'])).
% 2.42/2.63  thf('157', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('158', plain,
% 2.42/2.63      ((((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.42/2.63          = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_A))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['156', '157'])).
% 2.42/2.63  thf('159', plain,
% 2.42/2.63      (((((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.42/2.63           = (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['73', '158'])).
% 2.42/2.63  thf('160', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('161', plain,
% 2.42/2.63      ((((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_C)
% 2.42/2.63          = (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['159', '160'])).
% 2.42/2.63  thf('162', plain,
% 2.42/2.63      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.42/2.63          (k1_relat_1 @ sk_B))
% 2.42/2.63         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.42/2.63         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['72', '161'])).
% 2.42/2.63  thf('163', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.42/2.63         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.42/2.63            (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['49', '162'])).
% 2.42/2.63  thf('164', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('165', plain,
% 2.42/2.63      (((~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 2.42/2.63         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.42/2.63            (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['163', '164'])).
% 2.42/2.63  thf('166', plain,
% 2.42/2.63      (((~ (v1_relat_1 @ sk_A)
% 2.42/2.63         | ~ (v1_funct_1 @ sk_A)
% 2.42/2.63         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.42/2.63            (k1_relat_1 @ sk_B))))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup-', [status(thm)], ['48', '165'])).
% 2.42/2.63  thf('167', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('168', plain, ((v1_funct_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('169', plain,
% 2.42/2.63      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 2.42/2.63         (k1_relat_1 @ sk_B)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['166', '167', '168'])).
% 2.42/2.63  thf('170', plain,
% 2.42/2.63      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 2.42/2.63         | ~ (v1_relat_1 @ sk_A)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('sup+', [status(thm)], ['41', '169'])).
% 2.42/2.63  thf('171', plain, ((v1_relat_1 @ sk_A)),
% 2.42/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.63  thf('172', plain,
% 2.42/2.63      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 2.42/2.63      inference('demod', [status(thm)], ['170', '171'])).
% 2.42/2.63  thf('173', plain,
% 2.42/2.63      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 2.42/2.63         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 2.42/2.63      inference('split', [status(esa)], ['20'])).
% 2.42/2.63  thf('174', plain,
% 2.42/2.63      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 2.42/2.63       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 2.42/2.63      inference('sup-', [status(thm)], ['172', '173'])).
% 2.42/2.63  thf('175', plain, ($false),
% 2.42/2.63      inference('sat_resolution*', [status(thm)],
% 2.42/2.63                ['1', '22', '23', '39', '40', '174'])).
% 2.42/2.63  
% 2.42/2.63  % SZS output end Refutation
% 2.42/2.63  
% 2.42/2.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
