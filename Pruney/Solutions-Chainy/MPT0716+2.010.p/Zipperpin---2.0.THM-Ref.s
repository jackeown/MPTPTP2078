%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPJ8yQnzjk

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 495 expanded)
%              Number of leaves         :   25 ( 148 expanded)
%              Depth                    :   29
%              Number of atoms          : 1190 (7198 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) )
        = sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) )
        = sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) )
      = sk_C_1 )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
        = sk_C_1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
      = sk_C_1 )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

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

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('38',plain,
    ( ( ( sk_C_1
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
        = sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      = sk_C_1 )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','43','44','45'])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['21','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','20','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('63',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('66',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','20','59','65'])).

thf('67',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
        = sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
      = sk_C_1 )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('79',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','59','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
      = sk_C_1 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['71','72','80','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['61','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPJ8yQnzjk
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 230 iterations in 0.276s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.73  thf(t171_funct_1, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.55/0.73               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.55/0.73                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.73              ( ![C:$i]:
% 0.55/0.73                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.55/0.73                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.55/0.73                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.55/0.73        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.55/0.73        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.55/0.73       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))) | 
% 0.55/0.73       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf(d3_tarski, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (![X1 : $i, X3 : $i]:
% 0.55/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.55/0.73        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('split', [status(esa)], ['4'])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.55/0.73          | (r2_hidden @ X0 @ X2)
% 0.55/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      ((![X0 : $i]:
% 0.55/0.73          ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.55/0.73           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      ((![X0 : $i]:
% 0.55/0.73          ((r1_tarski @ sk_C_1 @ X0)
% 0.55/0.73           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.55/0.73              (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '7'])).
% 0.55/0.73  thf(t44_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( v1_relat_1 @ B ) =>
% 0.55/0.73           ( r1_tarski @
% 0.55/0.73             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (![X13 : $i, X14 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X13)
% 0.55/0.73          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.55/0.73             (k1_relat_1 @ X14))
% 0.55/0.73          | ~ (v1_relat_1 @ X14))),
% 0.55/0.73      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.55/0.73          | (r2_hidden @ X0 @ X2)
% 0.55/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('11', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X1)
% 0.55/0.73          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.55/0.73          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      ((![X0 : $i]:
% 0.55/0.73          ((r1_tarski @ sk_C_1 @ X0)
% 0.55/0.73           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 0.55/0.73           | ~ (v1_relat_1 @ sk_B)
% 0.55/0.73           | ~ (v1_relat_1 @ sk_A)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['8', '11'])).
% 0.55/0.73  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      ((![X0 : $i]:
% 0.55/0.73          ((r1_tarski @ sk_C_1 @ X0)
% 0.55/0.73           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (![X1 : $i, X3 : $i]:
% 0.55/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.55/0.73         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.55/0.73         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.55/0.73       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(t148_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.55/0.73          | ~ (v1_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.55/0.73  thf(fc8_funct_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.55/0.73         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X21 : $i, X22 : $i]:
% 0.55/0.73         (~ (v1_funct_1 @ X21)
% 0.55/0.73          | ~ (v1_relat_1 @ X21)
% 0.55/0.73          | (v1_funct_1 @ (k7_relat_1 @ X21 @ X22)))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.55/0.73  thf(dt_k7_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      (![X6 : $i, X7 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.73  thf(t112_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ![C:$i]:
% 0.55/0.73         ( ( v1_relat_1 @ C ) =>
% 0.55/0.73           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.55/0.73             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X8)
% 0.55/0.73          | ((k7_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.55/0.73              = (k5_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X8))
% 0.55/0.73          | ~ (v1_relat_1 @ X9))),
% 0.55/0.73      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.55/0.73  thf(dt_k5_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.55/0.73       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X4 : $i, X5 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X4)
% 0.55/0.73          | ~ (v1_relat_1 @ X5)
% 0.55/0.73          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('split', [status(esa)], ['4'])).
% 0.55/0.73  thf(t91_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.73         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X19 : $i, X20 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.55/0.73          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.55/0.73          | ~ (v1_relat_1 @ X20))),
% 0.55/0.73      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.55/0.73         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C_1))
% 0.55/0.73             = (sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ sk_B)
% 0.55/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.55/0.73         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C_1))
% 0.55/0.73             = (sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['25', '28'])).
% 0.55/0.73  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C_1))
% 0.55/0.73          = (sk_C_1)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.73           = (sk_C_1))
% 0.55/0.73         | ~ (v1_relat_1 @ sk_A)
% 0.55/0.73         | ~ (v1_relat_1 @ sk_B)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup+', [status(thm)], ['24', '32'])).
% 0.55/0.73  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.73          = (sk_C_1)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.55/0.73  thf(t27_funct_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.73           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.55/0.73             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X23 : $i, X24 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X23)
% 0.55/0.73          | ~ (v1_funct_1 @ X23)
% 0.55/0.73          | (r1_tarski @ (k2_relat_1 @ X23) @ (k1_relat_1 @ X24))
% 0.55/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X23 @ X24)) != (k1_relat_1 @ X23))
% 0.55/0.73          | ~ (v1_funct_1 @ X24)
% 0.55/0.73          | ~ (v1_relat_1 @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (((((sk_C_1) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)))
% 0.55/0.73         | ~ (v1_relat_1 @ sk_B)
% 0.55/0.73         | ~ (v1_funct_1 @ sk_B)
% 0.55/0.73         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73            (k1_relat_1 @ sk_B))
% 0.55/0.73         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C_1))
% 0.55/0.73         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.55/0.73  thf('40', plain,
% 0.55/0.73      (![X19 : $i, X20 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.55/0.73          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.55/0.73          | ~ (v1_relat_1 @ X20))),
% 0.55/0.73      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ sk_A)
% 0.55/0.73         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) = (sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('43', plain,
% 0.55/0.73      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) = (sk_C_1)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.55/0.73  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      (((((sk_C_1) != (sk_C_1))
% 0.55/0.73         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73            (k1_relat_1 @ sk_B))
% 0.55/0.73         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C_1))
% 0.55/0.73         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['38', '43', '44', '45'])).
% 0.55/0.73  thf('47', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))
% 0.55/0.73         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C_1))
% 0.55/0.73         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73            (k1_relat_1 @ sk_B))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ sk_A)
% 0.55/0.73         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73            (k1_relat_1 @ sk_B))
% 0.55/0.73         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['23', '47'])).
% 0.55/0.73  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('50', plain,
% 0.55/0.73      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73          (k1_relat_1 @ sk_B))
% 0.55/0.73         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C_1))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      (((~ (v1_relat_1 @ sk_A)
% 0.55/0.73         | ~ (v1_funct_1 @ sk_A)
% 0.55/0.73         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73            (k1_relat_1 @ sk_B))))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['22', '50'])).
% 0.55/0.73  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('53', plain, ((v1_funct_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('54', plain,
% 0.55/0.73      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.55/0.73         (k1_relat_1 @ sk_B)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.55/0.73  thf('55', plain,
% 0.55/0.73      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.55/0.73         | ~ (v1_relat_1 @ sk_A)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('sup+', [status(thm)], ['21', '54'])).
% 0.55/0.73  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('57', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.55/0.73         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.55/0.73      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.73  thf('58', plain,
% 0.55/0.73      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.55/0.73         <= (~
% 0.55/0.73             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))) | 
% 0.55/0.73       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['2', '20', '59'])).
% 0.55/0.73  thf('61', plain,
% 0.55/0.73      (~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('simpl_trail', [status(thm)], ['1', '60'])).
% 0.55/0.73  thf('62', plain,
% 0.55/0.73      (![X6 : $i, X7 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.73  thf('63', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.55/0.73        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('64', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.55/0.73         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.55/0.73      inference('split', [status(esa)], ['63'])).
% 0.55/0.73  thf('65', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))) | 
% 0.55/0.73       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.73      inference('split', [status(esa)], ['63'])).
% 0.55/0.73  thf('66', plain,
% 0.55/0.73      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['2', '20', '59', '65'])).
% 0.55/0.73  thf('67', plain,
% 0.55/0.73      ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))),
% 0.55/0.73      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.55/0.73          | ~ (v1_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.55/0.74  thf(t46_relat_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( v1_relat_1 @ B ) =>
% 0.55/0.74           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.74             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X15)
% 0.55/0.74          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15)) = (k1_relat_1 @ X16))
% 0.55/0.74          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 0.55/0.74          | ~ (v1_relat_1 @ X16))),
% 0.55/0.74      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.55/0.74  thf('70', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k1_relat_1 @ X2))
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.55/0.74          | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.55/0.74              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ X2))),
% 0.55/0.74      inference('sup-', [status(thm)], ['68', '69'])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_B)
% 0.55/0.74        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.74            = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)))
% 0.55/0.74        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1))
% 0.55/0.74        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['67', '70'])).
% 0.55/0.74  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('73', plain,
% 0.55/0.74      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.55/0.74         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.55/0.74      inference('split', [status(esa)], ['4'])).
% 0.55/0.74  thf('74', plain,
% 0.55/0.74      (![X19 : $i, X20 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.55/0.74          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.55/0.74          | ~ (v1_relat_1 @ X20))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.55/0.74  thf('75', plain,
% 0.55/0.74      (((~ (v1_relat_1 @ sk_A)
% 0.55/0.74         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) = (sk_C_1))))
% 0.55/0.74         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['73', '74'])).
% 0.55/0.74  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('77', plain,
% 0.55/0.74      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) = (sk_C_1)))
% 0.55/0.74         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['75', '76'])).
% 0.55/0.74  thf('78', plain,
% 0.55/0.74      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.55/0.74       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.55/0.74      inference('split', [status(esa)], ['4'])).
% 0.55/0.74  thf('79', plain, (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['2', '20', '59', '78'])).
% 0.55/0.74  thf('80', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.55/0.74  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('82', plain,
% 0.55/0.74      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.74          = (sk_C_1))
% 0.55/0.74        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['71', '72', '80', '81'])).
% 0.55/0.74  thf('83', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_A)
% 0.55/0.74        | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.74            = (sk_C_1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['62', '82'])).
% 0.55/0.74  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('85', plain,
% 0.55/0.74      (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.55/0.74         = (sk_C_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['83', '84'])).
% 0.55/0.74  thf('86', plain,
% 0.55/0.74      (![X4 : $i, X5 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X4)
% 0.55/0.74          | ~ (v1_relat_1 @ X5)
% 0.55/0.74          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.55/0.74  thf('87', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X8)
% 0.55/0.74          | ((k7_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.55/0.74              = (k5_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X8))
% 0.55/0.74          | ~ (v1_relat_1 @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.55/0.74  thf(t89_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( r1_tarski @
% 0.55/0.74         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.55/0.74  thf('88', plain,
% 0.55/0.74      (![X17 : $i, X18 : $i]:
% 0.55/0.74         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)) @ 
% 0.55/0.74           (k1_relat_1 @ X17))
% 0.55/0.74          | ~ (v1_relat_1 @ X17))),
% 0.55/0.74      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.55/0.74  thf('89', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((r1_tarski @ 
% 0.55/0.74           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.55/0.74           (k1_relat_1 @ (k5_relat_1 @ X2 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ X2)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['87', '88'])).
% 0.55/0.74  thf('90', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | (r1_tarski @ 
% 0.55/0.74             (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.55/0.74             (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['86', '89'])).
% 0.55/0.74  thf('91', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((r1_tarski @ 
% 0.55/0.74           (k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 0.55/0.74           (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['90'])).
% 0.55/0.74  thf('92', plain,
% 0.55/0.74      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.55/0.74        | ~ (v1_relat_1 @ sk_B)
% 0.55/0.74        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.74      inference('sup+', [status(thm)], ['85', '91'])).
% 0.55/0.74  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('94', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('95', plain,
% 0.55/0.74      ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.55/0.74  thf('96', plain, ($false), inference('demod', [status(thm)], ['61', '95'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
