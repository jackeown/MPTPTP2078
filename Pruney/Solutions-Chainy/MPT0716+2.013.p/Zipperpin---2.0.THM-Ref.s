%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ieQhJ9CKa

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  841 (1967 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X14 @ X13 ) @ X15 )
      | ( r1_tarski @ X13 @ ( k10_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('40',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k9_relat_1 @ X6 @ X4 ) @ ( k9_relat_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','36','37','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ieQhJ9CKa
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 610 iterations in 0.445s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.70/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.70/0.89  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.70/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.89  thf(t171_funct_1, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.89           ( ![C:$i]:
% 0.70/0.89             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.70/0.89               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.70/0.89                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.89          ( ![B:$i]:
% 0.70/0.89            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.89              ( ![C:$i]:
% 0.70/0.89                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.70/0.89                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.70/0.89                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.70/0.89        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.70/0.89       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf(d3_tarski, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.89          | (r2_hidden @ X0 @ X2)
% 0.70/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.70/0.89           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ sk_C_1 @ X0)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.70/0.89              (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['2', '5'])).
% 0.70/0.89  thf(t44_relat_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( v1_relat_1 @ B ) =>
% 0.70/0.89           ( r1_tarski @
% 0.70/0.89             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X9)
% 0.70/0.89          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.70/0.89             (k1_relat_1 @ X10))
% 0.70/0.89          | ~ (v1_relat_1 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.89          | (r2_hidden @ X0 @ X2)
% 0.70/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X0)
% 0.70/0.89          | ~ (v1_relat_1 @ X1)
% 0.70/0.89          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.70/0.89          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ sk_C_1 @ X0)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 0.70/0.89           | ~ (v1_relat_1 @ sk_B)
% 0.70/0.89           | ~ (v1_relat_1 @ sk_A)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['6', '9'])).
% 0.70/0.89  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ sk_C_1 @ X0)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.70/0.89         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.70/0.89        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.70/0.89        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.70/0.89         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.70/0.89       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['16', '18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.70/0.89       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.70/0.89       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['17'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.70/0.89        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.70/0.89         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['21'])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf(t163_funct_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.70/0.89       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.70/0.89           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.70/0.89         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.70/0.89          | ~ (r1_tarski @ (k9_relat_1 @ X14 @ X13) @ X15)
% 0.70/0.89          | (r1_tarski @ X13 @ (k10_relat_1 @ X14 @ X15))
% 0.70/0.89          | ~ (v1_funct_1 @ X14)
% 0.70/0.89          | ~ (v1_relat_1 @ X14))),
% 0.70/0.89      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          (~ (v1_relat_1 @ sk_A)
% 0.70/0.89           | ~ (v1_funct_1 @ sk_A)
% 0.70/0.89           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.70/0.89           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.70/0.89  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.70/0.89           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.70/0.89      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 0.70/0.89             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['22', '28'])).
% 0.70/0.89  thf(t182_relat_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( v1_relat_1 @ B ) =>
% 0.70/0.89           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.70/0.89             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X7)
% 0.70/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.70/0.89              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 0.70/0.89          | ~ (v1_relat_1 @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.70/0.89         <= (~
% 0.70/0.89             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('split', [status(esa)], ['17'])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.70/0.89         | ~ (v1_relat_1 @ sk_A)
% 0.70/0.89         | ~ (v1_relat_1 @ sk_B)))
% 0.70/0.89         <= (~
% 0.70/0.89             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.89  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89         <= (~
% 0.70/0.89             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.70/0.89       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.70/0.89       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['29', '35'])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.70/0.89       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['21'])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X7)
% 0.70/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.70/0.89              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 0.70/0.89          | ~ (v1_relat_1 @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.70/0.89         | ~ (v1_relat_1 @ sk_A)
% 0.70/0.89         | ~ (v1_relat_1 @ sk_B)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['39', '40'])).
% 0.70/0.89  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.70/0.89  thf(t156_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ C ) =>
% 0.70/0.89       ( ( r1_tarski @ A @ B ) =>
% 0.70/0.89         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X4 @ X5)
% 0.70/0.89          | ~ (v1_relat_1 @ X6)
% 0.70/0.89          | (r1_tarski @ (k9_relat_1 @ X6 @ X4) @ (k9_relat_1 @ X6 @ X5)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ 
% 0.70/0.89            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89           | ~ (v1_relat_1 @ X0)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.89          | (r2_hidden @ X0 @ X2)
% 0.70/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      ((![X0 : $i, X1 : $i]:
% 0.70/0.89          (~ (v1_relat_1 @ X0)
% 0.70/0.89           | (r2_hidden @ X1 @ 
% 0.70/0.89              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89           | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ sk_C_1))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      ((![X0 : $i, X1 : $i]:
% 0.70/0.89          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_C_1)) @ 
% 0.70/0.89              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.70/0.89           | ~ (v1_relat_1 @ X0)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['38', '48'])).
% 0.70/0.89  thf(t145_funct_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.89       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X11 : $i, X12 : $i]:
% 0.70/0.89         ((r1_tarski @ (k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X12)) @ X12)
% 0.70/0.89          | ~ (v1_funct_1 @ X11)
% 0.70/0.89          | ~ (v1_relat_1 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.89          | (r2_hidden @ X0 @ X2)
% 0.70/0.89          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X1)
% 0.70/0.89          | ~ (v1_funct_1 @ X1)
% 0.70/0.89          | (r2_hidden @ X2 @ X0)
% 0.70/0.89          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          (~ (v1_relat_1 @ sk_A)
% 0.70/0.89           | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.70/0.89              (k1_relat_1 @ sk_B))
% 0.70/0.89           | ~ (v1_funct_1 @ sk_A)
% 0.70/0.89           | ~ (v1_relat_1 @ sk_A)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['49', '52'])).
% 0.70/0.89  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('55', plain, ((v1_funct_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.70/0.89           | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.70/0.89              (k1_relat_1 @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X1 : $i, X3 : $i]:
% 0.70/0.89         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.70/0.89         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.70/0.89         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.70/0.89         <= (~
% 0.70/0.89             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['17'])).
% 0.70/0.89  thf('62', plain,
% 0.70/0.89      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.70/0.89       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['60', '61'])).
% 0.70/0.89  thf('63', plain, ($false),
% 0.70/0.89      inference('sat_resolution*', [status(thm)],
% 0.70/0.89                ['1', '19', '20', '36', '37', '62'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
