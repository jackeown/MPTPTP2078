%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OpNI4dYBwK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 133 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  765 (1942 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X15 @ X14 ) @ X16 )
      | ( r1_tarski @ X14 @ ( k10_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('32',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('40',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k9_relat_1 @ X9 @ X7 ) @ ( k9_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','36','37','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OpNI4dYBwK
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:38:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 134 iterations in 0.119s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(t171_funct_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.39/0.59               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.39/0.59                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59              ( ![C:$i]:
% 0.39/0.59                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.39/0.59                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.39/0.59                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.39/0.59        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.39/0.59       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf(d3_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X1 : $i, X3 : $i]:
% 0.39/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.59          | (r2_hidden @ X0 @ X2)
% 0.39/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.39/0.59           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((r1_tarski @ sk_C_1 @ X0)
% 0.39/0.59           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.39/0.59              (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '5'])).
% 0.39/0.59  thf(t21_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.59           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.39/0.59             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.39/0.59               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X17)
% 0.39/0.59          | ~ (v1_funct_1 @ X17)
% 0.39/0.59          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X19)))
% 0.39/0.59          | (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.39/0.59          | ~ (v1_funct_1 @ X19)
% 0.39/0.59          | ~ (v1_relat_1 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((r1_tarski @ sk_C_1 @ X0)
% 0.39/0.59           | ~ (v1_relat_1 @ sk_B)
% 0.39/0.59           | ~ (v1_funct_1 @ sk_B)
% 0.39/0.59           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 0.39/0.59           | ~ (v1_funct_1 @ sk_A)
% 0.39/0.59           | ~ (v1_relat_1 @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.59  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((r1_tarski @ sk_C_1 @ X0)
% 0.39/0.59           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X1 : $i, X3 : $i]:
% 0.39/0.59         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.39/0.59         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.39/0.59        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.39/0.59        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.39/0.59         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.39/0.59       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.39/0.59       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.39/0.59        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.39/0.59         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.39/0.59      inference('split', [status(esa)], ['21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf(t163_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.59       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.39/0.59           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.39/0.59         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.39/0.59          | ~ (r1_tarski @ (k9_relat_1 @ X15 @ X14) @ X16)
% 0.39/0.59          | (r1_tarski @ X14 @ (k10_relat_1 @ X15 @ X16))
% 0.39/0.59          | ~ (v1_funct_1 @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (~ (v1_relat_1 @ sk_A)
% 0.39/0.59           | ~ (v1_funct_1 @ sk_A)
% 0.39/0.59           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.39/0.59           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.59  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.39/0.59           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.39/0.59      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 0.39/0.59             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '28'])).
% 0.39/0.59  thf(t182_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( v1_relat_1 @ B ) =>
% 0.39/0.59           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.39/0.59             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X10)
% 0.39/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.39/0.59              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.39/0.59          | ~ (v1_relat_1 @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('split', [status(esa)], ['17'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.39/0.59         | ~ (v1_relat_1 @ sk_A)
% 0.39/0.59         | ~ (v1_relat_1 @ sk_B)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.39/0.59       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '35'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.39/0.59       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.39/0.59      inference('split', [status(esa)], ['21'])).
% 0.39/0.59  thf(t145_funct_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.59       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i]:
% 0.39/0.59         ((r1_tarski @ (k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X13)) @ X13)
% 0.39/0.59          | ~ (v1_funct_1 @ X12)
% 0.39/0.59          | ~ (v1_relat_1 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X10)
% 0.39/0.59          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.39/0.59              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.39/0.59          | ~ (v1_relat_1 @ X11))),
% 0.39/0.59      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.39/0.59         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf(t156_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ C ) =>
% 0.39/0.59       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.59         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X7 @ X8)
% 0.39/0.59          | ~ (v1_relat_1 @ X9)
% 0.39/0.59          | (r1_tarski @ (k9_relat_1 @ X9 @ X7) @ (k9_relat_1 @ X9 @ X8)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      ((![X0 : $i]:
% 0.39/0.60          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ 
% 0.39/0.60            (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.39/0.60           | ~ (v1_relat_1 @ X0)))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.60  thf(t1_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.60       ( r1_tarski @ A @ C ) ))).
% 0.39/0.60  thf('43', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.60         (~ (r1_tarski @ X4 @ X5)
% 0.39/0.60          | ~ (r1_tarski @ X5 @ X6)
% 0.39/0.60          | (r1_tarski @ X4 @ X6))),
% 0.39/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (~ (v1_relat_1 @ X0)
% 0.39/0.60           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.39/0.60           | ~ (r1_tarski @ 
% 0.39/0.60                (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))) @ 
% 0.39/0.60                X1)))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (~ (r1_tarski @ 
% 0.39/0.60              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.39/0.60              X0)
% 0.39/0.60           | ~ (v1_relat_1 @ sk_A)
% 0.39/0.60           | ~ (v1_relat_1 @ sk_B)
% 0.39/0.60           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C_1) @ X0)
% 0.39/0.60           | ~ (v1_relat_1 @ X1)))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['39', '44'])).
% 0.39/0.60  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (~ (r1_tarski @ 
% 0.39/0.60              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.39/0.60              X0)
% 0.39/0.60           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C_1) @ X0)
% 0.39/0.60           | ~ (v1_relat_1 @ X1)))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      (((~ (v1_relat_1 @ sk_A)
% 0.39/0.60         | ~ (v1_funct_1 @ sk_A)
% 0.39/0.60         | ~ (v1_relat_1 @ sk_A)
% 0.39/0.60         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['38', '48'])).
% 0.39/0.60  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('51', plain, ((v1_funct_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.39/0.60         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.39/0.60         <= (~
% 0.39/0.60             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.39/0.60      inference('split', [status(esa)], ['17'])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.39/0.60       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('56', plain, ($false),
% 0.39/0.60      inference('sat_resolution*', [status(thm)],
% 0.39/0.60                ['1', '19', '20', '36', '37', '55'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
