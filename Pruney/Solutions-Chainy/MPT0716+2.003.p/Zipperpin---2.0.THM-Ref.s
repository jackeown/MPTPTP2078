%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y3prPkXCDf

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 208 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          : 1034 (2873 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X19 ) ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X12 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('35',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X21 @ X20 ) @ X22 )
      | ( r1_tarski @ X20 @ ( k10_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('45',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('60',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','66'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf('76',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','49','50','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y3prPkXCDf
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.84  % Solved by: fo/fo7.sh
% 0.63/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.84  % done 591 iterations in 0.368s
% 0.63/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.84  % SZS output start Refutation
% 0.63/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.63/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.63/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.63/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.63/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.63/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.63/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.63/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.63/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.63/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.63/0.84  thf(t171_funct_1, conjecture,
% 0.63/0.84    (![A:$i]:
% 0.63/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.63/0.84       ( ![B:$i]:
% 0.63/0.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.84           ( ![C:$i]:
% 0.63/0.84             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.63/0.84               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.63/0.84                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.63/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.84    (~( ![A:$i]:
% 0.63/0.84        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.63/0.84          ( ![B:$i]:
% 0.63/0.84            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.84              ( ![C:$i]:
% 0.63/0.84                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.63/0.84                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.63/0.84                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.63/0.84    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.63/0.84  thf('0', plain,
% 0.63/0.84      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.63/0.84        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('1', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.63/0.84      inference('split', [status(esa)], ['0'])).
% 0.63/0.84  thf(t145_funct_1, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.84       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.63/0.84  thf('2', plain,
% 0.63/0.84      (![X18 : $i, X19 : $i]:
% 0.63/0.84         ((r1_tarski @ (k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X19)) @ X19)
% 0.63/0.84          | ~ (v1_funct_1 @ X18)
% 0.63/0.84          | ~ (v1_relat_1 @ X18))),
% 0.63/0.84      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.63/0.84  thf(t182_relat_1, axiom,
% 0.63/0.84    (![A:$i]:
% 0.63/0.84     ( ( v1_relat_1 @ A ) =>
% 0.63/0.84       ( ![B:$i]:
% 0.63/0.84         ( ( v1_relat_1 @ B ) =>
% 0.63/0.84           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.63/0.84             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.63/0.84  thf('3', plain,
% 0.63/0.84      (![X16 : $i, X17 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X16)
% 0.63/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.63/0.84              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 0.63/0.84          | ~ (v1_relat_1 @ X17))),
% 0.63/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.63/0.84  thf('4', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.63/0.84        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('5', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('split', [status(esa)], ['4'])).
% 0.63/0.84  thf('6', plain,
% 0.63/0.84      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84         | ~ (v1_relat_1 @ sk_A)
% 0.63/0.84         | ~ (v1_relat_1 @ sk_B)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup+', [status(thm)], ['3', '5'])).
% 0.63/0.84  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('9', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.63/0.84  thf(t12_xboole_1, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.63/0.84  thf('10', plain,
% 0.63/0.84      (![X10 : $i, X11 : $i]:
% 0.63/0.84         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.63/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.63/0.84  thf('11', plain,
% 0.63/0.84      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.84  thf(d10_xboole_0, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.63/0.84  thf('12', plain,
% 0.63/0.84      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.63/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.84  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.63/0.84      inference('simplify', [status(thm)], ['12'])).
% 0.63/0.84  thf(t11_xboole_1, axiom,
% 0.63/0.84    (![A:$i,B:$i,C:$i]:
% 0.63/0.84     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.63/0.84  thf('14', plain,
% 0.63/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.63/0.84         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.63/0.84      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.63/0.84  thf('15', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.63/0.84      inference('sup-', [status(thm)], ['13', '14'])).
% 0.63/0.84  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.63/0.84      inference('simplify', [status(thm)], ['12'])).
% 0.63/0.84  thf(t158_relat_1, axiom,
% 0.63/0.84    (![A:$i,B:$i,C:$i]:
% 0.63/0.84     ( ( v1_relat_1 @ C ) =>
% 0.63/0.84       ( ![D:$i]:
% 0.63/0.84         ( ( v1_relat_1 @ D ) =>
% 0.63/0.84           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.63/0.84             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.63/0.84  thf('17', plain,
% 0.63/0.84      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X12)
% 0.63/0.84          | (r1_tarski @ (k9_relat_1 @ X13 @ X14) @ (k9_relat_1 @ X12 @ X15))
% 0.63/0.84          | ~ (r1_tarski @ X13 @ X12)
% 0.63/0.84          | ~ (r1_tarski @ X14 @ X15)
% 0.63/0.84          | ~ (v1_relat_1 @ X13))),
% 0.63/0.84      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.63/0.84  thf('18', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X0)
% 0.63/0.84          | ~ (r1_tarski @ X2 @ X1)
% 0.63/0.84          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.63/0.84          | ~ (v1_relat_1 @ X0))),
% 0.63/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.63/0.84  thf('19', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.63/0.84          | ~ (r1_tarski @ X2 @ X1)
% 0.63/0.84          | ~ (v1_relat_1 @ X0))),
% 0.63/0.84      inference('simplify', [status(thm)], ['18'])).
% 0.63/0.84  thf('20', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X2)
% 0.63/0.84          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.63/0.84             (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['15', '19'])).
% 0.63/0.84  thf('21', plain,
% 0.63/0.84      (![X10 : $i, X11 : $i]:
% 0.63/0.84         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.63/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.63/0.84  thf('22', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X2)
% 0.63/0.84          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.63/0.84              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.63/0.84              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.63/0.84  thf('23', plain,
% 0.63/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.63/0.84         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.63/0.84      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.63/0.84  thf('24', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.63/0.84         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.63/0.84          | ~ (v1_relat_1 @ X2)
% 0.63/0.84          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.63/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.63/0.84  thf('25', plain,
% 0.63/0.84      ((![X0 : $i, X1 : $i]:
% 0.63/0.84          (~ (r1_tarski @ 
% 0.63/0.84              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.63/0.84              X0)
% 0.63/0.84           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C_1) @ X0)
% 0.63/0.84           | ~ (v1_relat_1 @ X1)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['11', '24'])).
% 0.63/0.84  thf('26', plain,
% 0.63/0.84      (((~ (v1_relat_1 @ sk_A)
% 0.63/0.84         | ~ (v1_funct_1 @ sk_A)
% 0.63/0.84         | ~ (v1_relat_1 @ sk_A)
% 0.63/0.84         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['2', '25'])).
% 0.63/0.84  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('30', plain,
% 0.63/0.84      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.63/0.84  thf('31', plain,
% 0.63/0.84      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.63/0.84        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.63/0.84        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('32', plain,
% 0.63/0.84      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.63/0.84         <= (~
% 0.63/0.84             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.63/0.84      inference('split', [status(esa)], ['31'])).
% 0.63/0.84  thf('33', plain,
% 0.63/0.84      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['30', '32'])).
% 0.63/0.84  thf('34', plain,
% 0.63/0.84      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.63/0.84       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.63/0.84      inference('split', [status(esa)], ['31'])).
% 0.63/0.84  thf('35', plain,
% 0.63/0.84      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.63/0.84         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.63/0.84      inference('split', [status(esa)], ['0'])).
% 0.63/0.84  thf('36', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.63/0.84      inference('split', [status(esa)], ['4'])).
% 0.63/0.84  thf(t163_funct_1, axiom,
% 0.63/0.84    (![A:$i,B:$i,C:$i]:
% 0.63/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.63/0.84       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.63/0.84           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.63/0.84         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.63/0.84  thf('37', plain,
% 0.63/0.84      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.63/0.84         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.63/0.84          | ~ (r1_tarski @ (k9_relat_1 @ X21 @ X20) @ X22)
% 0.63/0.84          | (r1_tarski @ X20 @ (k10_relat_1 @ X21 @ X22))
% 0.63/0.84          | ~ (v1_funct_1 @ X21)
% 0.63/0.84          | ~ (v1_relat_1 @ X21))),
% 0.63/0.84      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.63/0.84  thf('38', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          (~ (v1_relat_1 @ sk_A)
% 0.63/0.84           | ~ (v1_funct_1 @ sk_A)
% 0.63/0.84           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.63/0.84           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.63/0.84  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('40', plain, ((v1_funct_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('41', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.63/0.84           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.63/0.84      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.63/0.84  thf('42', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 0.63/0.84             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['35', '41'])).
% 0.63/0.84  thf('43', plain,
% 0.63/0.84      (![X16 : $i, X17 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X16)
% 0.63/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.63/0.84              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 0.63/0.84          | ~ (v1_relat_1 @ X17))),
% 0.63/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.63/0.84  thf('44', plain,
% 0.63/0.84      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (~
% 0.63/0.84             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('split', [status(esa)], ['31'])).
% 0.63/0.84  thf('45', plain,
% 0.63/0.84      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84         | ~ (v1_relat_1 @ sk_A)
% 0.63/0.84         | ~ (v1_relat_1 @ sk_B)))
% 0.63/0.84         <= (~
% 0.63/0.84             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.63/0.84  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('48', plain,
% 0.63/0.84      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (~
% 0.63/0.84             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.63/0.84  thf('49', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.63/0.84       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['42', '48'])).
% 0.63/0.84  thf('50', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.63/0.84      inference('split', [status(esa)], ['4'])).
% 0.63/0.84  thf('51', plain,
% 0.63/0.84      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.84  thf(d3_tarski, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.63/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.63/0.84  thf('52', plain,
% 0.63/0.84      (![X1 : $i, X3 : $i]:
% 0.63/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.63/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.84  thf('53', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.63/0.84      inference('sup-', [status(thm)], ['13', '14'])).
% 0.63/0.84  thf('54', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.63/0.84          | (r2_hidden @ X0 @ X2)
% 0.63/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.63/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.84  thf('55', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.63/0.84      inference('sup-', [status(thm)], ['53', '54'])).
% 0.63/0.84  thf('56', plain,
% 0.63/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.63/0.84         ((r1_tarski @ X0 @ X1)
% 0.63/0.84          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['52', '55'])).
% 0.63/0.84  thf('57', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.63/0.84            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84           | (r1_tarski @ sk_C_1 @ X0)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup+', [status(thm)], ['51', '56'])).
% 0.63/0.84  thf('58', plain,
% 0.63/0.84      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.63/0.84  thf('59', plain,
% 0.63/0.84      (![X16 : $i, X17 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X16)
% 0.63/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 0.63/0.84              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 0.63/0.84          | ~ (v1_relat_1 @ X17))),
% 0.63/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.63/0.84  thf('60', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('split', [status(esa)], ['4'])).
% 0.63/0.84  thf('61', plain,
% 0.63/0.84      (![X10 : $i, X11 : $i]:
% 0.63/0.84         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.63/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.63/0.84  thf('62', plain,
% 0.63/0.84      ((((k2_xboole_0 @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.63/0.84          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['60', '61'])).
% 0.63/0.84  thf('63', plain,
% 0.63/0.84      (((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84           = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.63/0.84         | ~ (v1_relat_1 @ sk_A)
% 0.63/0.84         | ~ (v1_relat_1 @ sk_B)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup+', [status(thm)], ['59', '62'])).
% 0.63/0.84  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('66', plain,
% 0.63/0.84      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.63/0.84  thf('67', plain,
% 0.63/0.84      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.63/0.84          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup+', [status(thm)], ['58', '66'])).
% 0.63/0.84  thf(t21_funct_1, axiom,
% 0.63/0.84    (![A:$i,B:$i]:
% 0.63/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.63/0.84       ( ![C:$i]:
% 0.63/0.84         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.63/0.84           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.63/0.84             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.63/0.84               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.63/0.84  thf('68', plain,
% 0.63/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.63/0.84         (~ (v1_relat_1 @ X23)
% 0.63/0.84          | ~ (v1_funct_1 @ X23)
% 0.63/0.84          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ (k5_relat_1 @ X23 @ X25)))
% 0.63/0.84          | (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.63/0.84          | ~ (v1_funct_1 @ X25)
% 0.63/0.84          | ~ (v1_relat_1 @ X25))),
% 0.63/0.84      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.63/0.84  thf('69', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84           | ~ (v1_relat_1 @ sk_B)
% 0.63/0.84           | ~ (v1_funct_1 @ sk_B)
% 0.63/0.84           | (r2_hidden @ X0 @ (k1_relat_1 @ sk_A))
% 0.63/0.84           | ~ (v1_funct_1 @ sk_A)
% 0.63/0.84           | ~ (v1_relat_1 @ sk_A)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['67', '68'])).
% 0.63/0.84  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('72', plain, ((v1_funct_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('73', plain, ((v1_relat_1 @ sk_A)),
% 0.63/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.84  thf('74', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.63/0.84           | (r2_hidden @ X0 @ (k1_relat_1 @ sk_A))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.63/0.84  thf('75', plain,
% 0.63/0.84      ((![X0 : $i]:
% 0.63/0.84          ((r1_tarski @ sk_C_1 @ X0)
% 0.63/0.84           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['57', '74'])).
% 0.63/0.84  thf('76', plain,
% 0.63/0.84      (![X1 : $i, X3 : $i]:
% 0.63/0.84         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.63/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.84  thf('77', plain,
% 0.63/0.84      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.63/0.84         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('sup-', [status(thm)], ['75', '76'])).
% 0.63/0.84  thf('78', plain,
% 0.63/0.84      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.63/0.84         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.63/0.84      inference('simplify', [status(thm)], ['77'])).
% 0.63/0.84  thf('79', plain,
% 0.63/0.84      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.63/0.84         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.63/0.84      inference('split', [status(esa)], ['31'])).
% 0.63/0.84  thf('80', plain,
% 0.63/0.84      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.63/0.84       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.63/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.63/0.84  thf('81', plain, ($false),
% 0.63/0.84      inference('sat_resolution*', [status(thm)],
% 0.63/0.84                ['1', '33', '34', '49', '50', '80'])).
% 0.63/0.84  
% 0.63/0.84  % SZS output end Refutation
% 0.63/0.84  
% 0.63/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
