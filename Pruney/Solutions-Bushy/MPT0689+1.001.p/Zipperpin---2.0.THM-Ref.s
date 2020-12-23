%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0689+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D0ZOnKltYI

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:20 EST 2020

% Result     : Theorem 24.85s
% Output     : Refutation 24.85s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 366 expanded)
%              Number of leaves         :   21 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          : 2058 (5519 expanded)
%              Number of equality atoms :  133 ( 377 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t144_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
              & ! [C: $i] :
                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) )
                 != ( k1_tarski @ C ) ) )
      <=> ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
                & ! [C: $i] :
                    ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) )
                   != ( k1_tarski @ C ) ) )
        <=> ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_funct_1])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
        = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
      | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( ( k1_funct_1 @ X18 @ ( sk_B @ X18 ) )
        = ( k1_funct_1 @ X18 @ ( sk_C_2 @ X18 ) ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('7',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_B @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

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

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('34',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( sk_B @ sk_A )
        = ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) )
        = ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('37',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('38',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C_2 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,
    ( ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k1_tarski @ ( sk_C_3 @ ( k1_funct_1 @ sk_A @ ( sk_C_2 @ sk_A ) ) ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['35','47'])).

thf('49',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ ( k1_tarski @ ( sk_B @ sk_A ) ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('51',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( sk_C_2 @ sk_A )
        = ( sk_B @ sk_A ) ) )
   <= ! [X22: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
          = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
        | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v2_funct_1 @ sk_A )
   <= ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( ( sk_C_2 @ sk_A )
      = ( sk_B @ sk_A ) )
   <= ( ~ ( v2_funct_1 @ sk_A )
      & ! [X22: $i] :
          ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
            = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
          | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X18: $i] :
      ( ( ( sk_B @ X18 )
       != ( sk_C_2 @ X18 ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('55',plain,
    ( ( ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ( ~ ( v2_funct_1 @ sk_A )
      & ! [X22: $i] :
          ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
            = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
          | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( ( sk_B @ sk_A )
       != ( sk_B @ sk_A ) )
      | ( v2_funct_1 @ sk_A ) )
   <= ( ~ ( v2_funct_1 @ sk_A )
      & ! [X22: $i] :
          ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
            = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
          | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v2_funct_1 @ sk_A )
   <= ( ~ ( v2_funct_1 @ sk_A )
      & ! [X22: $i] :
          ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
            = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
          | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ sk_A )
   <= ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ~ ! [X22: $i] :
          ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X22 ) )
            = ( k1_tarski @ ( sk_C_3 @ X22 ) ) )
          | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X21: $i] :
        ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
       != ( k1_tarski @ X21 ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X2 @ X4 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ ( sk_C @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k10_relat_1 @ X2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k10_relat_1 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X1 )
      | ( ( k1_funct_1 @ X2 @ ( sk_C @ ( k10_relat_1 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('71',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('72',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( v2_funct_1 @ sk_A )
   <= ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('77',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_funct_1 @ X18 @ X19 )
       != ( k1_funct_1 @ X18 @ X20 ) )
      | ( X19 = X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = X0 )
        | ( ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
         != ( k1_funct_1 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v2_funct_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('88',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( sk_B_1
        = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( sk_B_1
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = X0 )
        | ( sk_B_1
         != ( k1_funct_1 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v2_funct_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
        | ( sk_B_1
         != ( k1_funct_1 @ sk_A @ X0 ) )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = X0 ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','93'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( ( k10_relat_1 @ sk_A @ X1 )
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 )
          = X0 )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 ) )
        | ( sk_B_1
         != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 ) ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k10_relat_1 @ sk_A @ X1 )
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 )
          = X0 )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 ) )
        | ( sk_B_1
         != ( k1_funct_1 @ sk_A @ ( sk_C @ ( k10_relat_1 @ sk_A @ X1 ) @ X0 ) ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B_1 != X0 )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 )
          = X1 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ X1 ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 ) )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 )
          = X1 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ X1 ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B_1 != X0 )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 )
          = X1 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ X1 ) )
        | ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 ) )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) ) @ X1 )
          = X1 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ X1 ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ! [X1: $i] :
        ( ( ( sk_D_2 @ sk_B_1 @ sk_A )
          = ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X1 ) )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
          = ( k1_tarski @ X1 ) )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X1 )
          = X1 ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ( ( sk_D_2 @ sk_B_1 @ sk_A )
         != X0 )
        | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
          = X0 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
          = ( k1_tarski @ X0 ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
        = ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('107',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
       != ( sk_D_2 @ sk_B_1 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('109',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('110',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) @ X0 )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B_1
      = ( k1_funct_1 @ sk_A @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('113',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ sk_B_1 @ X0 ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_B_1 @ sk_A ) @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
       != ( sk_D_2 @ sk_B_1 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','116'])).

thf('118',plain,
    ( ( ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
       != ( sk_D_2 @ sk_B_1 @ sk_A ) )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
      | ( ( sk_C @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( sk_D_2 @ sk_B_1 @ sk_A ) )
        = ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('120',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ! [X21: $i] :
        ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
       != ( k1_tarski @ X21 ) )
   <= ! [X21: $i] :
        ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
       != ( k1_tarski @ X21 ) ) ),
    inference(split,[status(esa)],['62'])).

thf('122',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
      & ( v2_funct_1 @ sk_A )
      & ! [X21: $i] :
          ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
         != ( k1_tarski @ X21 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ! [X21: $i] :
          ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
         != ( k1_tarski @ X21 ) )
    | ~ ( v2_funct_1 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','61','63','123'])).


%------------------------------------------------------------------------------
