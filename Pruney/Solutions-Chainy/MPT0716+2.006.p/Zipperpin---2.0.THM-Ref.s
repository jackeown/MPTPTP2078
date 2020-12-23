%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QqHYmGVWr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 139 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  800 (1910 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
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

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X19 @ X18 ) @ X20 )
      | ( r1_tarski @ X18 @ ( k10_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ ( k10_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k9_relat_1 @ X9 @ X10 ) @ ( k9_relat_1 @ X8 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','15','31','32','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QqHYmGVWr
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 763 iterations in 0.378s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.82  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.58/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(t171_funct_1, conjecture,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.82           ( ![C:$i]:
% 0.58/0.82             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.58/0.82               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.82                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i]:
% 0.58/0.82        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82          ( ![B:$i]:
% 0.58/0.82            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.82              ( ![C:$i]:
% 0.58/0.82                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.58/0.82                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.82                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.58/0.82        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.58/0.82       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf(t44_relat_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( v1_relat_1 @ A ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( v1_relat_1 @ B ) =>
% 0.58/0.82           ( r1_tarski @
% 0.58/0.82             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X14 : $i, X15 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ X14)
% 0.58/0.82          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 0.58/0.82             (k1_relat_1 @ X15))
% 0.58/0.82          | ~ (v1_relat_1 @ X15))),
% 0.58/0.82      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.58/0.82         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf(t12_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i]:
% 0.58/0.82         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.83      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.83  thf(t11_xboole_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.58/0.83  thf('6', plain,
% 0.58/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.83         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.58/0.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.58/0.83  thf('7', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.58/0.83           | (r1_tarski @ sk_C @ X0)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.83  thf('8', plain,
% 0.58/0.83      (((~ (v1_relat_1 @ sk_A)
% 0.58/0.83         | ~ (v1_relat_1 @ sk_B)
% 0.58/0.83         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['2', '7'])).
% 0.58/0.83  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('11', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.58/0.83  thf('12', plain,
% 0.58/0.83      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.58/0.83        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.58/0.83        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('13', plain,
% 0.58/0.83      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.58/0.83         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.58/0.83      inference('split', [status(esa)], ['12'])).
% 0.58/0.83  thf('14', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.58/0.83       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['11', '13'])).
% 0.58/0.83  thf('15', plain,
% 0.58/0.83      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.58/0.83       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.58/0.83      inference('split', [status(esa)], ['12'])).
% 0.58/0.83  thf('16', plain,
% 0.58/0.83      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.58/0.83        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('17', plain,
% 0.58/0.83      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.58/0.83         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.58/0.83      inference('split', [status(esa)], ['16'])).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf(t163_funct_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.58/0.83       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.58/0.83           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.58/0.83         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.83         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.58/0.83          | ~ (r1_tarski @ (k9_relat_1 @ X19 @ X18) @ X20)
% 0.58/0.83          | (r1_tarski @ X18 @ (k10_relat_1 @ X19 @ X20))
% 0.58/0.83          | ~ (v1_funct_1 @ X19)
% 0.58/0.83          | ~ (v1_relat_1 @ X19))),
% 0.58/0.83      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          (~ (v1_relat_1 @ sk_A)
% 0.58/0.83           | ~ (v1_funct_1 @ sk_A)
% 0.58/0.83           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.58/0.83           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.83  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('22', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.58/0.83           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.58/0.83      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.58/0.83  thf('24', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.58/0.83             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['17', '23'])).
% 0.58/0.83  thf(t182_relat_1, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( v1_relat_1 @ B ) =>
% 0.58/0.83           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.58/0.83             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.58/0.83  thf('25', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X12)
% 0.58/0.83          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.58/0.83              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.58/0.83          | ~ (v1_relat_1 @ X13))),
% 0.58/0.83      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('split', [status(esa)], ['12'])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.58/0.83         | ~ (v1_relat_1 @ sk_A)
% 0.58/0.83         | ~ (v1_relat_1 @ sk_B)))
% 0.58/0.83         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.83  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('30', plain,
% 0.58/0.83      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.58/0.83         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.58/0.83  thf('31', plain,
% 0.58/0.83      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.58/0.83       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['24', '30'])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.58/0.83      inference('split', [status(esa)], ['16'])).
% 0.58/0.83  thf(t145_funct_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.83       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      (![X16 : $i, X17 : $i]:
% 0.58/0.83         ((r1_tarski @ (k9_relat_1 @ X16 @ (k10_relat_1 @ X16 @ X17)) @ X17)
% 0.58/0.83          | ~ (v1_funct_1 @ X16)
% 0.58/0.83          | ~ (v1_relat_1 @ X16))),
% 0.58/0.83      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X12)
% 0.58/0.83          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.58/0.83              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.58/0.83          | ~ (v1_relat_1 @ X13))),
% 0.58/0.83      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.58/0.83  thf('35', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('36', plain,
% 0.58/0.83      ((((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.58/0.83         | ~ (v1_relat_1 @ sk_A)
% 0.58/0.83         | ~ (v1_relat_1 @ sk_B)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('39', plain,
% 0.58/0.83      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.58/0.83  thf('40', plain,
% 0.58/0.83      (![X6 : $i, X7 : $i]:
% 0.58/0.83         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.58/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.83  thf('41', plain,
% 0.58/0.83      ((((k2_xboole_0 @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.58/0.83          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.83  thf(d10_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.58/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.83  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.83      inference('simplify', [status(thm)], ['42'])).
% 0.58/0.83  thf('44', plain,
% 0.58/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.83         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.58/0.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.58/0.83  thf('45', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.83  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.83      inference('simplify', [status(thm)], ['42'])).
% 0.58/0.83  thf(t158_relat_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( v1_relat_1 @ C ) =>
% 0.58/0.83       ( ![D:$i]:
% 0.58/0.83         ( ( v1_relat_1 @ D ) =>
% 0.58/0.83           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.58/0.83             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.58/0.83  thf('47', plain,
% 0.58/0.83      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X8)
% 0.58/0.83          | (r1_tarski @ (k9_relat_1 @ X9 @ X10) @ (k9_relat_1 @ X8 @ X11))
% 0.58/0.83          | ~ (r1_tarski @ X9 @ X8)
% 0.58/0.83          | ~ (r1_tarski @ X10 @ X11)
% 0.58/0.83          | ~ (v1_relat_1 @ X9))),
% 0.58/0.83      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.58/0.83  thf('48', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X0)
% 0.58/0.83          | ~ (r1_tarski @ X2 @ X1)
% 0.58/0.83          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.58/0.83          | ~ (v1_relat_1 @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.83  thf('49', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.58/0.83          | ~ (r1_tarski @ X2 @ X1)
% 0.58/0.83          | ~ (v1_relat_1 @ X0))),
% 0.58/0.83      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X2)
% 0.58/0.83          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.58/0.83             (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['45', '49'])).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      (![X6 : $i, X7 : $i]:
% 0.58/0.83         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.58/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.83  thf('52', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         (~ (v1_relat_1 @ X2)
% 0.58/0.83          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.58/0.83              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.58/0.83              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.83  thf('53', plain,
% 0.58/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.83         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.58/0.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.58/0.83  thf('54', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.83         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.58/0.83          | ~ (v1_relat_1 @ X2)
% 0.58/0.83          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.58/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.83  thf('55', plain,
% 0.58/0.83      ((![X0 : $i, X1 : $i]:
% 0.58/0.83          (~ (r1_tarski @ 
% 0.58/0.83              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.58/0.83              X0)
% 0.58/0.83           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C) @ X0)
% 0.58/0.83           | ~ (v1_relat_1 @ X1)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['41', '54'])).
% 0.58/0.83  thf('56', plain,
% 0.58/0.83      (((~ (v1_relat_1 @ sk_A)
% 0.58/0.83         | ~ (v1_funct_1 @ sk_A)
% 0.58/0.83         | ~ (v1_relat_1 @ sk_A)
% 0.58/0.83         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['33', '55'])).
% 0.58/0.83  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('58', plain, ((v1_funct_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('60', plain,
% 0.58/0.83      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.58/0.83         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.58/0.83  thf('61', plain,
% 0.58/0.83      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.58/0.83         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.58/0.83      inference('split', [status(esa)], ['12'])).
% 0.58/0.83  thf('62', plain,
% 0.58/0.83      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.83  thf('63', plain, ($false),
% 0.58/0.83      inference('sat_resolution*', [status(thm)],
% 0.58/0.83                ['1', '14', '15', '31', '32', '62'])).
% 0.58/0.83  
% 0.58/0.83  % SZS output end Refutation
% 0.58/0.83  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
