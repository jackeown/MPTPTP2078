%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lr5GLCzfLg

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 400 expanded)
%              Number of leaves         :   14 ( 112 expanded)
%              Depth                    :   23
%              Number of atoms          : 1078 (7017 expanded)
%              Number of equality atoms :   68 ( 636 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ! [C: $i] :
                    ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                   => ( ( k1_funct_1 @ A @ C )
                      = ( k1_funct_1 @ B @ C ) ) ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X15 )
        = ( k1_funct_1 @ sk_B @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X15 )
        = ( k1_funct_1 @ sk_B @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_B = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ X0 ) )
      | ( sk_B = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ sk_A @ X15 )
        = ( k1_funct_1 @ sk_B @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( X14
       != ( k1_funct_1 @ X13 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X0 @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) )
    | ( sk_B = sk_A )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( sk_B = sk_A )
    | ( ( sk_D @ sk_A @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_D @ sk_A @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_B = sk_A )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( k1_funct_1 @ X13 @ X12 ) ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_A @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_A @ ( sk_C @ sk_A @ sk_B ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('76',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_D @ sk_A @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('78',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['66','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lr5GLCzfLg
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 16:57:25 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 172 iterations in 0.121s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(t9_funct_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.57           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.22/0.57               ( ![C:$i]:
% 0.22/0.57                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.57                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.22/0.57             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.57              ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.22/0.57                  ( ![C:$i]:
% 0.22/0.57                    ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.57                      ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.22/0.57                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t9_funct_1])).
% 0.22/0.57  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d2_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ B ) =>
% 0.22/0.57           ( ( ( A ) = ( B ) ) <=>
% 0.22/0.57             ( ![C:$i,D:$i]:
% 0.22/0.57               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.22/0.57                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.22/0.57  thf(d4_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.57       ( ![C:$i]:
% 0.22/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.57           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.57         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.22/0.57          | (r2_hidden @ X5 @ X8)
% 0.22/0.57          | ((X8) != (k1_relat_1 @ X7)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.57         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.22/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X0) = (X1))
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.57         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.22/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         (((k1_funct_1 @ sk_A @ X15) = (k1_funct_1 @ sk_B @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('8', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         (((k1_funct_1 @ sk_A @ X15) = (k1_funct_1 @ sk_B @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.57          | ((sk_B) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))
% 0.22/0.57              = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.57  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ X0))
% 0.22/0.57          | ((sk_B) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((k1_funct_1 @ sk_A @ (sk_C @ X0 @ sk_B))
% 0.22/0.57              = (k1_funct_1 @ sk_B @ (sk_C @ X0 @ sk_B))))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | ((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.57            = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.57        | ((sk_B) = (sk_A)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['0', '12'])).
% 0.22/0.57  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | ((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.57            = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.22/0.57        | ((sk_B) = (sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain, (((sk_A) != (sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | ((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.57            = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         (((k1_funct_1 @ sk_A @ X15) = (k1_funct_1 @ sk_B @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.57         = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.22/0.57      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf(t8_funct_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 0.22/0.57          | ((X14) != (k1_funct_1 @ X13 @ X12))
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.22/0.57          | ~ (v1_funct_1 @ X13)
% 0.22/0.57          | ~ (v1_relat_1 @ X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X13)
% 0.22/0.57          | ~ (v1_funct_1 @ X13)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.22/0.57          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_C @ X0 @ X1) @ 
% 0.22/0.57              (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))) @ 
% 0.22/0.57             X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '22'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_funct_1 @ X0)
% 0.22/0.57          | (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_C @ X0 @ X1) @ 
% 0.22/0.57              (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))) @ 
% 0.22/0.57             X0)
% 0.22/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.57          (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.57         sk_A)
% 0.22/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.57        | ((sk_B) = (sk_A))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.57        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | ~ (v1_funct_1 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['19', '24'])).
% 0.22/0.57  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.57          (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.57         sk_A)
% 0.22/0.57        | ((sk_B) = (sk_A))
% 0.22/0.57        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.22/0.57  thf('30', plain, (((sk_A) != (sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.57          (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.57         sk_A)
% 0.22/0.57        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.57         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.22/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf('34', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.57        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.22/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X13)
% 0.22/0.57          | ~ (v1_funct_1 @ X13)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.22/0.57          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (((r2_hidden @ 
% 0.22/0.57         (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.57          (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.57         sk_B)
% 0.22/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.57        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      ((r2_hidden @ 
% 0.22/0.57        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.57         (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.57        sk_B)),
% 0.22/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.57         = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.22/0.57      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.22/0.57          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.22/0.57          | ~ (v1_funct_1 @ X13)
% 0.22/0.57          | ~ (v1_relat_1 @ X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X0) = (X1))
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X0)
% 0.22/0.57          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 0.22/0.57          | ~ (v1_funct_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X1)
% 0.22/0.57          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.22/0.57          | ((X0) = (X1))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.22/0.57          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.22/0.57          | ~ (v1_funct_1 @ X13)
% 0.22/0.57          | ~ (v1_relat_1 @ X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X1)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X1)
% 0.22/0.57          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X0)
% 0.22/0.57          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1)))
% 0.22/0.57          | ~ (v1_funct_1 @ X0)
% 0.22/0.57          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 0.22/0.57          | ~ (v1_funct_1 @ X1)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      ((((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.57        | ((sk_B) = (sk_A))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.57        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.57        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.22/0.57        | ~ (v1_funct_1 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['42', '49'])).
% 0.22/0.57  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('53', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('54', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      ((((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))
% 0.22/0.57        | ((sk_B) = (sk_A))
% 0.22/0.57        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))))),
% 0.22/0.57      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      ((((sk_B) = (sk_A))
% 0.22/0.57        | ((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))))),
% 0.22/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.57  thf('57', plain, (((sk_A) != (sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('58', plain,
% 0.22/0.57      (((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      ((r2_hidden @ 
% 0.22/0.57        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_B)),
% 0.22/0.57      inference('demod', [status(thm)], ['41', '58'])).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.22/0.57               X1)
% 0.22/0.57          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 0.22/0.57               X0)
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.57        | ((sk_B) = (sk_A))
% 0.22/0.57        | ~ (r2_hidden @ 
% 0.22/0.57             (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)
% 0.22/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.58  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('64', plain,
% 0.22/0.58      ((((sk_B) = (sk_A))
% 0.22/0.58        | ~ (r2_hidden @ 
% 0.22/0.58             (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A))),
% 0.22/0.58      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.58  thf('65', plain, (((sk_A) != (sk_B))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('66', plain,
% 0.22/0.58      (~ (r2_hidden @ 
% 0.22/0.58          (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.22/0.58  thf('67', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.22/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.58  thf('68', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('69', plain,
% 0.22/0.58      (![X12 : $i, X13 : $i]:
% 0.22/0.58         (~ (v1_relat_1 @ X13)
% 0.22/0.58          | ~ (v1_funct_1 @ X13)
% 0.22/0.58          | (r2_hidden @ (k4_tarski @ X12 @ (k1_funct_1 @ X13 @ X12)) @ X13)
% 0.22/0.58          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X13)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.58  thf('70', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.22/0.58          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A)
% 0.22/0.58          | ~ (v1_funct_1 @ sk_A)
% 0.22/0.58          | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.58  thf('71', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('73', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.22/0.58          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_A @ X0)) @ sk_A))),
% 0.22/0.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.22/0.58  thf('74', plain,
% 0.22/0.58      ((r2_hidden @ 
% 0.22/0.58        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.58         (k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.58        sk_A)),
% 0.22/0.58      inference('sup-', [status(thm)], ['67', '73'])).
% 0.22/0.58  thf('75', plain,
% 0.22/0.58      (((k1_funct_1 @ sk_A @ (sk_C @ sk_A @ sk_B))
% 0.22/0.58         = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.22/0.58      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.58  thf('76', plain,
% 0.22/0.58      ((r2_hidden @ 
% 0.22/0.58        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ 
% 0.22/0.58         (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B))) @ 
% 0.22/0.58        sk_A)),
% 0.22/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.58  thf('77', plain,
% 0.22/0.58      (((sk_D @ sk_A @ sk_B) = (k1_funct_1 @ sk_B @ (sk_C @ sk_A @ sk_B)))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.22/0.58  thf('78', plain,
% 0.22/0.58      ((r2_hidden @ 
% 0.22/0.58        (k4_tarski @ (sk_C @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B)) @ sk_A)),
% 0.22/0.58      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.58  thf('79', plain, ($false), inference('demod', [status(thm)], ['66', '78'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
