%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BjTpAXaz6L

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 209 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          : 1002 (2869 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
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

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k9_relat_1 @ X11 @ X9 ) @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('34',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
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

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X17 @ X16 ) @ X18 )
      | ( r1_tarski @ X16 @ ( k10_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','65'])).

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

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X21 ) ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','48','49','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BjTpAXaz6L
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 535 iterations in 0.275s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(t171_funct_1, conjecture,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.73           ( ![C:$i]:
% 0.53/0.73             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.53/0.73               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.53/0.73                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i]:
% 0.53/0.73        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.73          ( ![B:$i]:
% 0.53/0.73            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.73              ( ![C:$i]:
% 0.53/0.73                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.53/0.73                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.53/0.73                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.53/0.73        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('1', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf(t145_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.73       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      (![X14 : $i, X15 : $i]:
% 0.53/0.73         ((r1_tarski @ (k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X15)) @ X15)
% 0.53/0.73          | ~ (v1_funct_1 @ X14)
% 0.53/0.73          | ~ (v1_relat_1 @ X14))),
% 0.53/0.73      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.53/0.73  thf(t182_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( v1_relat_1 @ B ) =>
% 0.53/0.73           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.53/0.73             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X12)
% 0.53/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.53/0.73              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.53/0.73        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('split', [status(esa)], ['4'])).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.53/0.73         | ~ (v1_relat_1 @ sk_B)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['3', '5'])).
% 0.53/0.73  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.53/0.73  thf(t12_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X7 : $i, X8 : $i]:
% 0.53/0.73         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf(d3_tarski, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (![X1 : $i, X3 : $i]:
% 0.53/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X1 : $i, X3 : $i]:
% 0.53/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.73  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.73      inference('simplify', [status(thm)], ['14'])).
% 0.53/0.73  thf(t11_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.73         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.53/0.73      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.73  thf(t156_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ C ) =>
% 0.53/0.73       ( ( r1_tarski @ A @ B ) =>
% 0.53/0.73         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X9 @ X10)
% 0.53/0.73          | ~ (v1_relat_1 @ X11)
% 0.53/0.73          | (r1_tarski @ (k9_relat_1 @ X11 @ X9) @ (k9_relat_1 @ X11 @ X10)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.53/0.73           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.53/0.73          | ~ (v1_relat_1 @ X2))),
% 0.53/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      (![X7 : $i, X8 : $i]:
% 0.53/0.73         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X2)
% 0.53/0.73          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.53/0.73              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.53/0.73              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.73         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.53/0.73      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.73         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.53/0.73          | ~ (v1_relat_1 @ X2)
% 0.53/0.73          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.53/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      ((![X0 : $i, X1 : $i]:
% 0.53/0.73          (~ (r1_tarski @ 
% 0.53/0.73              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.53/0.73              X0)
% 0.53/0.73           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C_1) @ X0)
% 0.53/0.73           | ~ (v1_relat_1 @ X1)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['11', '23'])).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      (((~ (v1_relat_1 @ sk_A)
% 0.53/0.73         | ~ (v1_funct_1 @ sk_A)
% 0.53/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.53/0.73         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['2', '24'])).
% 0.53/0.73  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.53/0.73  thf('30', plain,
% 0.53/0.73      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.53/0.73        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.53/0.73        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.53/0.73         <= (~
% 0.53/0.73             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.53/0.73      inference('split', [status(esa)], ['30'])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['29', '31'])).
% 0.53/0.73  thf('33', plain,
% 0.53/0.73      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.53/0.73       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.53/0.73      inference('split', [status(esa)], ['30'])).
% 0.53/0.73  thf('34', plain,
% 0.53/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.53/0.73         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('35', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.53/0.73      inference('split', [status(esa)], ['4'])).
% 0.53/0.73  thf(t163_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.73       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.53/0.73           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.53/0.73         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.53/0.73          | ~ (r1_tarski @ (k9_relat_1 @ X17 @ X16) @ X18)
% 0.53/0.73          | (r1_tarski @ X16 @ (k10_relat_1 @ X17 @ X18))
% 0.53/0.73          | ~ (v1_funct_1 @ X17)
% 0.53/0.73          | ~ (v1_relat_1 @ X17))),
% 0.53/0.73      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          (~ (v1_relat_1 @ sk_A)
% 0.53/0.73           | ~ (v1_funct_1 @ sk_A)
% 0.53/0.73           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.53/0.73           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.73  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('39', plain, ((v1_funct_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('40', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.53/0.73           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.53/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 0.53/0.73             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['34', '40'])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      (![X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X12)
% 0.53/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.53/0.73              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (~
% 0.53/0.73             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('split', [status(esa)], ['30'])).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.53/0.73         | ~ (v1_relat_1 @ sk_B)))
% 0.53/0.73         <= (~
% 0.53/0.73             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.73  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (~
% 0.53/0.73             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.53/0.73       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['41', '47'])).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['4'])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      (![X1 : $i, X3 : $i]:
% 0.53/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.73  thf('52', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.73  thf('53', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.73          | (r2_hidden @ X0 @ X2)
% 0.53/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.73  thf('54', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.53/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.73  thf('55', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((r1_tarski @ X0 @ X1)
% 0.53/0.73          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['51', '54'])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.53/0.73            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73           | (r1_tarski @ sk_C_1 @ X0)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['50', '55'])).
% 0.53/0.73  thf('57', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf('58', plain,
% 0.53/0.73      (![X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X12)
% 0.53/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.53/0.73              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.53/0.73          | ~ (v1_relat_1 @ X13))),
% 0.53/0.73      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.53/0.73  thf('59', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('split', [status(esa)], ['4'])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      (![X7 : $i, X8 : $i]:
% 0.53/0.73         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.73  thf('61', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.53/0.73          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.73  thf('62', plain,
% 0.53/0.73      (((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73           = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.53/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.53/0.73         | ~ (v1_relat_1 @ sk_B)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['58', '61'])).
% 0.53/0.73  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.53/0.73  thf('66', plain,
% 0.53/0.73      ((((k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.53/0.73          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['57', '65'])).
% 0.53/0.73  thf(t21_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.73       ( ![C:$i]:
% 0.53/0.73         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.73           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.53/0.73             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.53/0.73               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.53/0.73  thf('67', plain,
% 0.53/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X19)
% 0.53/0.73          | ~ (v1_funct_1 @ X19)
% 0.53/0.73          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ (k5_relat_1 @ X19 @ X21)))
% 0.53/0.73          | (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.53/0.73          | ~ (v1_funct_1 @ X21)
% 0.53/0.73          | ~ (v1_relat_1 @ X21))),
% 0.53/0.73      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.53/0.73  thf('68', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73           | ~ (v1_relat_1 @ sk_B)
% 0.53/0.73           | ~ (v1_funct_1 @ sk_B)
% 0.53/0.73           | (r2_hidden @ X0 @ (k1_relat_1 @ sk_A))
% 0.53/0.73           | ~ (v1_funct_1 @ sk_A)
% 0.53/0.73           | ~ (v1_relat_1 @ sk_A)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.73  thf('69', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('71', plain, ((v1_funct_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          (~ (r2_hidden @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.53/0.73           | (r2_hidden @ X0 @ (k1_relat_1 @ sk_A))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.53/0.73  thf('74', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((r1_tarski @ sk_C_1 @ X0)
% 0.53/0.73           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['56', '73'])).
% 0.53/0.73  thf('75', plain,
% 0.53/0.73      (![X1 : $i, X3 : $i]:
% 0.53/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.73  thf('76', plain,
% 0.53/0.73      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.53/0.73         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.53/0.73  thf('77', plain,
% 0.53/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.53/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.53/0.73  thf('78', plain,
% 0.53/0.73      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.53/0.73         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.53/0.73      inference('split', [status(esa)], ['30'])).
% 0.53/0.73  thf('79', plain,
% 0.53/0.73      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['77', '78'])).
% 0.53/0.73  thf('80', plain, ($false),
% 0.53/0.73      inference('sat_resolution*', [status(thm)],
% 0.53/0.73                ['1', '32', '33', '48', '49', '79'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
