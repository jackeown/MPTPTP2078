%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1bhkLH52RD

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 322 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  854 (4718 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

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

thf('1',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k10_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k10_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('28',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k10_relat_1 @ X15 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('31',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X11 @ X12 ) @ ( k9_relat_1 @ X10 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X2 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('50',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['28','50','51'])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['6','52'])).

thf('54',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['28','50','51','56'])).

thf('58',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['28','50','51','60'])).

thf('62',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','61'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X25 @ X24 ) @ X26 )
      | ( r1_tarski @ X24 @ ( k10_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['53','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1bhkLH52RD
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:47:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 193 iterations in 0.159s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(t182_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( v1_relat_1 @ B ) =>
% 0.43/0.62           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.43/0.62             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X14)
% 0.43/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.43/0.62              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.43/0.62          | ~ (v1_relat_1 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.43/0.62  thf(t171_funct_1, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.43/0.62               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.62                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.62              ( ![C:$i]:
% 0.43/0.62                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.43/0.62                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.62                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.43/0.62        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.43/0.62        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('split', [status(esa)], ['1'])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.43/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.43/0.62         | ~ (v1_relat_1 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '2'])).
% 0.43/0.62  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X14)
% 0.43/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.43/0.62              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.43/0.62          | ~ (v1_relat_1 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.43/0.62  thf(d3_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X1 : $i, X3 : $i]:
% 0.43/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.43/0.62        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.62          | (r2_hidden @ X0 @ X2)
% 0.43/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.43/0.62           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r1_tarski @ sk_C_1 @ X0)
% 0.43/0.62           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.43/0.62              (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '12'])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.43/0.62            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.43/0.62           | ~ (v1_relat_1 @ sk_A)
% 0.43/0.62           | ~ (v1_relat_1 @ sk_B)
% 0.43/0.62           | (r1_tarski @ sk_C_1 @ X0)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['7', '13'])).
% 0.43/0.62  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.43/0.62            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.43/0.62           | (r1_tarski @ sk_C_1 @ X0)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.43/0.62  thf(d13_funct_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.62       ( ![B:$i,C:$i]:
% 0.43/0.62         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.43/0.62           ( ![D:$i]:
% 0.43/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.62               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.43/0.62                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.62         (((X19) != (k10_relat_1 @ X18 @ X17))
% 0.43/0.62          | (r2_hidden @ X20 @ (k1_relat_1 @ X18))
% 0.43/0.62          | ~ (r2_hidden @ X20 @ X19)
% 0.43/0.62          | ~ (v1_funct_1 @ X18)
% 0.43/0.62          | ~ (v1_relat_1 @ X18))),
% 0.43/0.62      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X18)
% 0.43/0.62          | ~ (v1_funct_1 @ X18)
% 0.43/0.62          | ~ (r2_hidden @ X20 @ (k10_relat_1 @ X18 @ X17))
% 0.43/0.62          | (r2_hidden @ X20 @ (k1_relat_1 @ X18)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r1_tarski @ sk_C_1 @ X0)
% 0.43/0.62           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 0.43/0.62           | ~ (v1_funct_1 @ sk_A)
% 0.43/0.62           | ~ (v1_relat_1 @ sk_A)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '19'])).
% 0.43/0.62  thf('21', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r1_tarski @ sk_C_1 @ X0)
% 0.43/0.62           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X1 : $i, X3 : $i]:
% 0.43/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.43/0.62         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.43/0.62         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['1'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.43/0.62       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.62  thf(t145_funct_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.62       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i]:
% 0.43/0.62         ((r1_tarski @ (k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X23)) @ X23)
% 0.43/0.62          | ~ (v1_funct_1 @ X22)
% 0.43/0.62          | ~ (v1_relat_1 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X14)
% 0.43/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.43/0.62              = (k10_relat_1 @ X15 @ (k1_relat_1 @ X14)))
% 0.43/0.62          | ~ (v1_relat_1 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.43/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.43/0.62         | ~ (v1_relat_1 @ sk_B)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.43/0.62  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.43/0.62  thf(d10_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.62  thf('37', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.43/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.43/0.62  thf(t158_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ C ) =>
% 0.43/0.62       ( ![D:$i]:
% 0.43/0.62         ( ( v1_relat_1 @ D ) =>
% 0.43/0.62           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.43/0.62             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X10)
% 0.43/0.62          | (r1_tarski @ (k9_relat_1 @ X11 @ X12) @ (k9_relat_1 @ X10 @ X13))
% 0.43/0.62          | ~ (r1_tarski @ X11 @ X10)
% 0.43/0.62          | ~ (r1_tarski @ X12 @ X13)
% 0.43/0.62          | ~ (v1_relat_1 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | ~ (r1_tarski @ X2 @ X1)
% 0.43/0.62          | (r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((r1_tarski @ (k9_relat_1 @ X0 @ X2) @ (k9_relat_1 @ X0 @ X1))
% 0.43/0.62          | ~ (r1_tarski @ X2 @ X1)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (v1_relat_1 @ X0)
% 0.43/0.62           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ 
% 0.43/0.62              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['35', '40'])).
% 0.43/0.62  thf(t1_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.43/0.62       ( r1_tarski @ A @ C ) ))).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X7 @ X8)
% 0.43/0.62          | ~ (r1_tarski @ X8 @ X9)
% 0.43/0.62          | (r1_tarski @ X7 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i]:
% 0.43/0.62          (~ (v1_relat_1 @ X0)
% 0.43/0.62           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.43/0.62           | ~ (r1_tarski @ 
% 0.43/0.62                (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.43/0.62                X1)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.43/0.62         | ~ (v1_funct_1 @ sk_A)
% 0.43/0.62         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.43/0.62         | ~ (v1_relat_1 @ sk_A)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['29', '43'])).
% 0.43/0.62  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('46', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['1'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))) | 
% 0.43/0.62       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.43/0.62       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.43/0.62       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['1'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['28', '50', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['6', '52'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.43/0.62        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.43/0.62         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['54'])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))) | 
% 0.43/0.62       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['54'])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['28', '50', '51', '56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.43/0.62         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.43/0.62       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['9'])).
% 0.43/0.62  thf('61', plain, (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['28', '50', '51', '60'])).
% 0.43/0.62  thf('62', plain, ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['59', '61'])).
% 0.43/0.62  thf(t163_funct_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.43/0.62           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.43/0.62         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.43/0.62          | ~ (r1_tarski @ (k9_relat_1 @ X25 @ X24) @ X26)
% 0.43/0.62          | (r1_tarski @ X24 @ (k10_relat_1 @ X25 @ X26))
% 0.43/0.62          | ~ (v1_funct_1 @ X25)
% 0.43/0.62          | ~ (v1_relat_1 @ X25))),
% 0.43/0.62      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ sk_A)
% 0.43/0.62          | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.43/0.62          | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.43/0.62  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('66', plain, ((v1_funct_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.43/0.62          | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['58', '67'])).
% 0.43/0.62  thf('69', plain, ($false), inference('demod', [status(thm)], ['53', '68'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
