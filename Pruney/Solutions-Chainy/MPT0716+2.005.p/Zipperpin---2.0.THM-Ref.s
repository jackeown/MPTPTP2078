%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdWE2KzId9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 146 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  841 (2012 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X12 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
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

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X19 @ X18 ) @ X20 )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('31',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k10_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k9_relat_1 @ X8 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','35','36','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdWE2KzId9
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:37:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 897 iterations in 0.514s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.98  thf(t171_funct_1, conjecture,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.98           ( ![C:$i]:
% 0.76/0.98             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.76/0.98               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.76/0.98                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i]:
% 0.76/0.98        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.98          ( ![B:$i]:
% 0.76/0.98            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.98              ( ![C:$i]:
% 0.76/0.98                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.76/0.98                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.76/0.98                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.76/0.98        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.76/0.98       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf(t167_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.76/0.98  thf('2', plain,
% 0.76/0.98      (![X12 : $i, X13 : $i]:
% 0.76/0.98         ((r1_tarski @ (k10_relat_1 @ X12 @ X13) @ (k1_relat_1 @ X12))
% 0.76/0.98          | ~ (v1_relat_1 @ X12))),
% 0.76/0.98      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.76/0.98  thf(t182_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( v1_relat_1 @ B ) =>
% 0.76/0.98           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.76/0.98             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.76/0.98  thf('3', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X14)
% 0.76/0.98          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.76/0.98              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.76/0.98          | ~ (v1_relat_1 @ X15))),
% 0.76/0.98      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.76/0.98  thf('4', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf(t12_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.98  thf('5', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.76/0.98          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.98  thf(t11_xboole_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.98         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.98  thf('8', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.76/0.98           | (r1_tarski @ sk_C @ X0)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.98  thf('9', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.76/0.98           | ~ (v1_relat_1 @ sk_A)
% 0.76/0.98           | ~ (v1_relat_1 @ sk_B)
% 0.76/0.98           | (r1_tarski @ sk_C @ X0)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['3', '8'])).
% 0.76/0.98  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('12', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.76/0.98           | (r1_tarski @ sk_C @ X0)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (((~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '12'])).
% 0.76/0.98  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['13', '14'])).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.76/0.98        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.76/0.98        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.76/0.98      inference('split', [status(esa)], ['16'])).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.76/0.98       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['15', '17'])).
% 0.76/0.98  thf('19', plain,
% 0.76/0.98      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.76/0.98       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.76/0.98       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('split', [status(esa)], ['16'])).
% 0.76/0.98  thf('20', plain,
% 0.76/0.98      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.76/0.98        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.76/0.98         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.76/0.98      inference('split', [status(esa)], ['20'])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf(t163_funct_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.98       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.98           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.76/0.98         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.76/0.98  thf('23', plain,
% 0.76/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.76/0.98         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.76/0.98          | ~ (r1_tarski @ (k9_relat_1 @ X19 @ X18) @ X20)
% 0.76/0.98          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ X20))
% 0.76/0.98          | ~ (v1_funct_1 @ X19)
% 0.76/0.98          | ~ (v1_relat_1 @ X19))),
% 0.76/0.98      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          (~ (v1_relat_1 @ sk_A)
% 0.76/0.98           | ~ (v1_funct_1 @ sk_A)
% 0.76/0.98           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.76/0.98           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.98  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.76/0.98           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.76/0.98      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.76/0.98             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['21', '27'])).
% 0.76/0.98  thf('29', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X14)
% 0.76/0.98          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.76/0.98              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.76/0.98          | ~ (v1_relat_1 @ X15))),
% 0.76/0.98      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.76/0.98  thf('30', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('split', [status(esa)], ['16'])).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.76/0.98         | ~ (v1_relat_1 @ sk_A)
% 0.76/0.98         | ~ (v1_relat_1 @ sk_B)))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.76/0.98  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.76/0.98         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.76/0.98       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.76/0.98       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['28', '34'])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.76/0.98       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('split', [status(esa)], ['20'])).
% 0.76/0.98  thf(t145_funct_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.98       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (![X16 : $i, X17 : $i]:
% 0.76/0.98         ((r1_tarski @ (k9_relat_1 @ X16 @ (k10_relat_1 @ X16 @ X17)) @ X17)
% 0.76/0.98          | ~ (v1_funct_1 @ X16)
% 0.76/0.98          | ~ (v1_relat_1 @ X16))),
% 0.76/0.98      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X14)
% 0.76/0.98          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.76/0.98              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.76/0.98          | ~ (v1_relat_1 @ X15))),
% 0.76/0.98      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.76/0.98  thf('39', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      ((((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.76/0.98         | ~ (v1_relat_1 @ sk_A)
% 0.76/0.98         | ~ (v1_relat_1 @ sk_B)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup+', [status(thm)], ['38', '39'])).
% 0.76/0.98  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      ((((k2_xboole_0 @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.76/0.98          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.98      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.98         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.98  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.98      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.98  thf(t158_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ C ) =>
% 0.76/0.98       ( ![D:$i]:
% 0.76/0.98         ( ( v1_relat_1 @ D ) =>
% 0.76/0.98           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.76/0.98             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.76/0.98  thf('51', plain,
% 0.76/0.98      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X8)
% 0.76/0.98          | (r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k9_relat_1 @ X8 @ X11))
% 0.76/0.98          | ~ (r1_tarski @ X9 @ X8)
% 0.76/0.98          | ~ (r1_tarski @ X10 @ X11)
% 0.76/0.98          | ~ (v1_relat_1 @ X9))),
% 0.76/0.98      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.76/0.98  thf('52', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X0)
% 0.76/0.98          | ~ (r1_tarski @ X2 @ X1)
% 0.76/0.98          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.76/0.98          | ~ (v1_relat_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.98  thf('53', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.76/0.98          | ~ (r1_tarski @ X2 @ X1)
% 0.76/0.98          | ~ (v1_relat_1 @ X0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.98  thf('54', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X2)
% 0.76/0.98          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.76/0.98             (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['49', '53'])).
% 0.76/0.98  thf('55', plain,
% 0.76/0.98      (![X6 : $i, X7 : $i]:
% 0.76/0.98         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.76/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.98  thf('56', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ X2)
% 0.76/0.98          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.76/0.98              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.76/0.98              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.98         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.76/0.98  thf('58', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.98         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.76/0.98          | ~ (v1_relat_1 @ X2)
% 0.76/0.98          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.76/0.98      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/0.98  thf('59', plain,
% 0.76/0.98      ((![X0 : $i, X1 : $i]:
% 0.76/0.98          (~ (r1_tarski @ 
% 0.76/0.98              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.76/0.98              X0)
% 0.76/0.98           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C) @ X0)
% 0.76/0.98           | ~ (v1_relat_1 @ X1)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['45', '58'])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      (((~ (v1_relat_1 @ sk_A)
% 0.76/0.98         | ~ (v1_funct_1 @ sk_A)
% 0.76/0.98         | ~ (v1_relat_1 @ sk_A)
% 0.76/0.98         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['37', '59'])).
% 0.76/0.98  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('62', plain, ((v1_funct_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('64', plain,
% 0.76/0.98      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.76/0.98         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.76/0.98      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.76/0.98  thf('65', plain,
% 0.76/0.98      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.76/0.98         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.76/0.98      inference('split', [status(esa)], ['16'])).
% 0.76/0.98  thf('66', plain,
% 0.76/0.98      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.76/0.98       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['64', '65'])).
% 0.76/0.98  thf('67', plain, ($false),
% 0.76/0.98      inference('sat_resolution*', [status(thm)],
% 0.76/0.98                ['1', '18', '19', '35', '36', '66'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
