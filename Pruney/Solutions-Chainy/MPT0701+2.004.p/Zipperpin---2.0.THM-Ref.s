%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F4OGkeu7cu

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:41 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 935 expanded)
%              Number of leaves         :   20 ( 264 expanded)
%              Depth                    :   26
%              Number of atoms          : 1210 (19301 expanded)
%              Number of equality atoms :   78 (2204 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t156_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( A
                    = ( k2_relat_1 @ B ) )
                  & ( ( k1_relat_1 @ C )
                    = A )
                  & ( ( k1_relat_1 @ D )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k5_relat_1 @ B @ D ) ) )
               => ( C = D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ! [D: $i] :
                ( ( ( v1_relat_1 @ D )
                  & ( v1_funct_1 @ D ) )
               => ( ( ( A
                      = ( k2_relat_1 @ B ) )
                    & ( ( k1_relat_1 @ C )
                      = A )
                    & ( ( k1_relat_1 @ D )
                      = A )
                    & ( ( k5_relat_1 @ B @ C )
                      = ( k5_relat_1 @ B @ D ) ) )
                 => ( C = D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_D_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
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

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_D_3 = sk_C_2 )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A )
    | ( sk_D_3 = sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_D_3 = sk_C_2 )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_C_2 != sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ sk_D_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( X17
       != ( k1_funct_1 @ X16 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_3 @ X0 ) ) @ sk_D_3 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_D_3 @ X0 ) ) @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ) @ sk_D_3 ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('29',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('30',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_2 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('31',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_2 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k1_funct_1 @ X12 @ ( k1_funct_1 @ X13 @ X14 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('42',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_2 @ X9 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('44',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_2 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( sk_C @ sk_C_2 @ sk_D_3 )
    = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','49'])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C_2 )
    = ( k5_relat_1 @ sk_B @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ X0 ) @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','49'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) )
      = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_B @ sk_C_2 ) @ ( sk_D_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_B ) )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
      = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['50','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ) @ sk_D_3 ),
    inference(demod,[status(thm)],['27','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('67',plain,(
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
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
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
    = ( k1_funct_1 @ sk_D_3 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
      = ( sk_D @ sk_C_2 @ sk_D_3 ) )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ( sk_D_3 = sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( sk_D @ sk_C_2 @ sk_D_3 )
      = ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
      = ( sk_D @ sk_C_2 @ sk_D_3 ) )
    | ( sk_D_3 = sk_C_2 )
    | ( ( sk_D @ sk_C_2 @ sk_D_3 )
      = ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ( sk_D_3 = sk_C_2 )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
      = ( sk_D @ sk_C_2 @ sk_D_3 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    sk_C_2 != sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
    = ( sk_D @ sk_C_2 @ sk_D_3 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( sk_D @ sk_C_2 @ sk_D_3 ) ) @ sk_D_3 ),
    inference(demod,[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( X1 = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( sk_D_3 = sk_C_2 )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( sk_D @ sk_C_2 @ sk_D_3 ) ) @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( k1_funct_1 @ X16 @ X15 ) ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) ) ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C @ sk_C_2 @ sk_D_3 ) )
    = ( sk_D @ sk_C_2 @ sk_D_3 ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('92',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_D_3 ) @ ( sk_D @ sk_C_2 @ sk_D_3 ) ) @ sk_C_2 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_D_3 = sk_C_2 ),
    inference(demod,[status(thm)],['81','82','92','93'])).

thf('95',plain,(
    sk_C_2 != sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F4OGkeu7cu
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.67/1.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.67/1.84  % Solved by: fo/fo7.sh
% 1.67/1.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.67/1.84  % done 1086 iterations in 1.382s
% 1.67/1.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.67/1.84  % SZS output start Refutation
% 1.67/1.84  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.67/1.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.67/1.84  thf(sk_B_type, type, sk_B: $i).
% 1.67/1.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.67/1.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.67/1.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.67/1.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.67/1.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.67/1.84  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.67/1.84  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.67/1.84  thf(sk_A_type, type, sk_A: $i).
% 1.67/1.84  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.67/1.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.67/1.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.67/1.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.67/1.84  thf(t156_funct_1, conjecture,
% 1.67/1.84    (![A:$i,B:$i]:
% 1.67/1.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.67/1.84       ( ![C:$i]:
% 1.67/1.84         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.67/1.84           ( ![D:$i]:
% 1.67/1.84             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 1.67/1.84               ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 1.67/1.84                   ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.67/1.84                   ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 1.67/1.84                   ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 1.67/1.84                 ( ( C ) = ( D ) ) ) ) ) ) ) ))).
% 1.67/1.84  thf(zf_stmt_0, negated_conjecture,
% 1.67/1.84    (~( ![A:$i,B:$i]:
% 1.67/1.84        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.67/1.84          ( ![C:$i]:
% 1.67/1.84            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.67/1.84              ( ![D:$i]:
% 1.67/1.84                ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 1.67/1.84                  ( ( ( ( A ) = ( k2_relat_1 @ B ) ) & 
% 1.67/1.84                      ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.67/1.84                      ( ( k1_relat_1 @ D ) = ( A ) ) & 
% 1.67/1.84                      ( ( k5_relat_1 @ B @ C ) = ( k5_relat_1 @ B @ D ) ) ) =>
% 1.67/1.84                    ( ( C ) = ( D ) ) ) ) ) ) ) ) )),
% 1.67/1.84    inference('cnf.neg', [status(esa)], [t156_funct_1])).
% 1.67/1.84  thf('0', plain, (((k1_relat_1 @ sk_D_3) = (sk_A))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('1', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf(d2_relat_1, axiom,
% 1.67/1.84    (![A:$i]:
% 1.67/1.84     ( ( v1_relat_1 @ A ) =>
% 1.67/1.84       ( ![B:$i]:
% 1.67/1.84         ( ( v1_relat_1 @ B ) =>
% 1.67/1.84           ( ( ( A ) = ( B ) ) <=>
% 1.67/1.84             ( ![C:$i,D:$i]:
% 1.67/1.84               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 1.67/1.84                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 1.67/1.84  thf('2', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X1))),
% 1.67/1.84      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.67/1.84  thf(t8_funct_1, axiom,
% 1.67/1.84    (![A:$i,B:$i,C:$i]:
% 1.67/1.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.67/1.84       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.67/1.84         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.67/1.84           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.67/1.84  thf('3', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.84         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.67/1.84          | (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | ~ (v1_relat_1 @ X16))),
% 1.67/1.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.67/1.84  thf('4', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X0) = (X1))
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.67/1.84      inference('sup-', [status(thm)], ['2', '3'])).
% 1.67/1.84  thf('5', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ~ (v1_relat_1 @ X1)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 1.67/1.84          | ((X0) = (X1))
% 1.67/1.84          | ~ (v1_relat_1 @ X0))),
% 1.67/1.84      inference('simplify', [status(thm)], ['4'])).
% 1.67/1.84  thf('6', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.84         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.67/1.84          | (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | ~ (v1_relat_1 @ X16))),
% 1.67/1.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.67/1.84  thf('7', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X1)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X1)
% 1.67/1.84          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 1.67/1.84      inference('sup-', [status(thm)], ['5', '6'])).
% 1.67/1.84  thf('8', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k1_relat_1 @ X1))
% 1.67/1.84          | ~ (v1_funct_1 @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X1))),
% 1.67/1.84      inference('simplify', [status(thm)], ['7'])).
% 1.67/1.84  thf('9', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         ((r2_hidden @ (sk_C @ sk_C_2 @ X0) @ sk_A)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X0) = (sk_C_2))
% 1.67/1.84          | ~ (v1_relat_1 @ sk_C_2)
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (sk_C @ sk_C_2 @ X0) @ (k1_relat_1 @ X0))
% 1.67/1.84          | ~ (v1_funct_1 @ sk_C_2))),
% 1.67/1.84      inference('sup+', [status(thm)], ['1', '8'])).
% 1.67/1.84  thf('10', plain, ((v1_relat_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('11', plain, ((v1_funct_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('12', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         ((r2_hidden @ (sk_C @ sk_C_2 @ X0) @ sk_A)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X0) = (sk_C_2))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (sk_C @ sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 1.67/1.84      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.67/1.84  thf('13', plain,
% 1.67/1.84      (((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)
% 1.67/1.84        | ~ (v1_funct_1 @ sk_D_3)
% 1.67/1.84        | ((sk_D_3) = (sk_C_2))
% 1.67/1.84        | ~ (v1_relat_1 @ sk_D_3)
% 1.67/1.84        | (r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A))),
% 1.67/1.84      inference('sup+', [status(thm)], ['0', '12'])).
% 1.67/1.84  thf('14', plain, ((v1_funct_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('15', plain, ((v1_relat_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('16', plain,
% 1.67/1.84      (((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)
% 1.67/1.84        | ((sk_D_3) = (sk_C_2))
% 1.67/1.84        | (r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A))),
% 1.67/1.84      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.67/1.84  thf('17', plain,
% 1.67/1.84      ((((sk_D_3) = (sk_C_2)) | (r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A))),
% 1.67/1.84      inference('simplify', [status(thm)], ['16'])).
% 1.67/1.84  thf('18', plain, (((sk_C_2) != (sk_D_3))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('19', plain, ((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 1.67/1.84  thf('20', plain, (((k1_relat_1 @ sk_D_3) = (sk_A))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('21', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 1.67/1.84          | ((X17) != (k1_funct_1 @ X16 @ X15))
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | ~ (v1_relat_1 @ X16))),
% 1.67/1.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.67/1.84  thf('22', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X16)
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 1.67/1.84          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 1.67/1.84      inference('simplify', [status(thm)], ['21'])).
% 1.67/1.84  thf('23', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_3 @ X0)) @ sk_D_3)
% 1.67/1.84          | ~ (v1_funct_1 @ sk_D_3)
% 1.67/1.84          | ~ (v1_relat_1 @ sk_D_3))),
% 1.67/1.84      inference('sup-', [status(thm)], ['20', '22'])).
% 1.67/1.84  thf('24', plain, ((v1_funct_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('25', plain, ((v1_relat_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('26', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_D_3 @ X0)) @ sk_D_3))),
% 1.67/1.84      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.67/1.84  thf('27', plain,
% 1.67/1.84      ((r2_hidden @ 
% 1.67/1.84        (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ 
% 1.67/1.84         (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3))) @ 
% 1.67/1.84        sk_D_3)),
% 1.67/1.84      inference('sup-', [status(thm)], ['19', '26'])).
% 1.67/1.84  thf('28', plain, ((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 1.67/1.84  thf('29', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf(d5_funct_1, axiom,
% 1.67/1.84    (![A:$i]:
% 1.67/1.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.67/1.84       ( ![B:$i]:
% 1.67/1.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.67/1.84           ( ![C:$i]:
% 1.67/1.84             ( ( r2_hidden @ C @ B ) <=>
% 1.67/1.84               ( ?[D:$i]:
% 1.67/1.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.67/1.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.67/1.84  thf('30', plain,
% 1.67/1.84      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.67/1.84         (((X8) != (k2_relat_1 @ X6))
% 1.67/1.84          | (r2_hidden @ (sk_D_2 @ X9 @ X6) @ (k1_relat_1 @ X6))
% 1.67/1.84          | ~ (r2_hidden @ X9 @ X8)
% 1.67/1.84          | ~ (v1_funct_1 @ X6)
% 1.67/1.84          | ~ (v1_relat_1 @ X6))),
% 1.67/1.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.67/1.84  thf('31', plain,
% 1.67/1.84      (![X6 : $i, X9 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X6)
% 1.67/1.84          | ~ (v1_funct_1 @ X6)
% 1.67/1.84          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 1.67/1.84          | (r2_hidden @ (sk_D_2 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 1.67/1.84      inference('simplify', [status(thm)], ['30'])).
% 1.67/1.84  thf('32', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.67/1.84          | ~ (v1_funct_1 @ sk_B)
% 1.67/1.84          | ~ (v1_relat_1 @ sk_B))),
% 1.67/1.84      inference('sup-', [status(thm)], ['29', '31'])).
% 1.67/1.84  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('35', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (sk_D_2 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 1.67/1.84      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.67/1.84  thf('36', plain,
% 1.67/1.84      ((r2_hidden @ (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B) @ 
% 1.67/1.84        (k1_relat_1 @ sk_B))),
% 1.67/1.84      inference('sup-', [status(thm)], ['28', '35'])).
% 1.67/1.84  thf(t23_funct_1, axiom,
% 1.67/1.84    (![A:$i,B:$i]:
% 1.67/1.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.67/1.84       ( ![C:$i]:
% 1.67/1.84         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.67/1.84           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.67/1.84             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.67/1.84               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 1.67/1.84  thf('37', plain,
% 1.67/1.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X12)
% 1.67/1.84          | ~ (v1_funct_1 @ X12)
% 1.67/1.84          | ((k1_funct_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 1.67/1.84              = (k1_funct_1 @ X12 @ (k1_funct_1 @ X13 @ X14)))
% 1.67/1.84          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 1.67/1.84          | ~ (v1_funct_1 @ X13)
% 1.67/1.84          | ~ (v1_relat_1 @ X13))),
% 1.67/1.84      inference('cnf', [status(esa)], [t23_funct_1])).
% 1.67/1.84  thf('38', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ sk_B)
% 1.67/1.84          | ~ (v1_funct_1 @ sk_B)
% 1.67/1.84          | ((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 1.67/1.84              (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))
% 1.67/1.84              = (k1_funct_1 @ X0 @ 
% 1.67/1.84                 (k1_funct_1 @ sk_B @ 
% 1.67/1.84                  (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ~ (v1_relat_1 @ X0))),
% 1.67/1.84      inference('sup-', [status(thm)], ['36', '37'])).
% 1.67/1.84  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('41', plain, ((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 1.67/1.84  thf('42', plain, (((sk_A) = (k2_relat_1 @ sk_B))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('43', plain,
% 1.67/1.84      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.67/1.84         (((X8) != (k2_relat_1 @ X6))
% 1.67/1.84          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_2 @ X9 @ X6)))
% 1.67/1.84          | ~ (r2_hidden @ X9 @ X8)
% 1.67/1.84          | ~ (v1_funct_1 @ X6)
% 1.67/1.84          | ~ (v1_relat_1 @ X6))),
% 1.67/1.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.67/1.84  thf('44', plain,
% 1.67/1.84      (![X6 : $i, X9 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X6)
% 1.67/1.84          | ~ (v1_funct_1 @ X6)
% 1.67/1.84          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 1.67/1.84          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_2 @ X9 @ X6))))),
% 1.67/1.84      inference('simplify', [status(thm)], ['43'])).
% 1.67/1.84  thf('45', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_2 @ X0 @ sk_B)))
% 1.67/1.84          | ~ (v1_funct_1 @ sk_B)
% 1.67/1.84          | ~ (v1_relat_1 @ sk_B))),
% 1.67/1.84      inference('sup-', [status(thm)], ['42', '44'])).
% 1.67/1.84  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('48', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | ((X0) = (k1_funct_1 @ sk_B @ (sk_D_2 @ X0 @ sk_B))))),
% 1.67/1.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.67/1.84  thf('49', plain,
% 1.67/1.84      (((sk_C @ sk_C_2 @ sk_D_3)
% 1.67/1.84         = (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B)))),
% 1.67/1.84      inference('sup-', [status(thm)], ['41', '48'])).
% 1.67/1.84  thf('50', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 1.67/1.84            (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))
% 1.67/1.84            = (k1_funct_1 @ X0 @ (sk_C @ sk_C_2 @ sk_D_3)))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ~ (v1_relat_1 @ X0))),
% 1.67/1.84      inference('demod', [status(thm)], ['38', '39', '40', '49'])).
% 1.67/1.84  thf('51', plain,
% 1.67/1.84      (((k5_relat_1 @ sk_B @ sk_C_2) = (k5_relat_1 @ sk_B @ sk_D_3))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('52', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (((k1_funct_1 @ (k5_relat_1 @ sk_B @ X0) @ 
% 1.67/1.84            (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))
% 1.67/1.84            = (k1_funct_1 @ X0 @ (sk_C @ sk_C_2 @ sk_D_3)))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ~ (v1_relat_1 @ X0))),
% 1.67/1.84      inference('demod', [status(thm)], ['38', '39', '40', '49'])).
% 1.67/1.84  thf('53', plain,
% 1.67/1.84      ((((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 1.67/1.84          (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))
% 1.67/1.84          = (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3)))
% 1.67/1.84        | ~ (v1_relat_1 @ sk_D_3)
% 1.67/1.84        | ~ (v1_funct_1 @ sk_D_3))),
% 1.67/1.84      inference('sup+', [status(thm)], ['51', '52'])).
% 1.67/1.84  thf('54', plain, ((v1_relat_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('55', plain, ((v1_funct_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('56', plain,
% 1.67/1.84      (((k1_funct_1 @ (k5_relat_1 @ sk_B @ sk_C_2) @ 
% 1.67/1.84         (sk_D_2 @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_B))
% 1.67/1.84         = (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3)))),
% 1.67/1.84      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.67/1.84  thf('57', plain,
% 1.67/1.84      ((((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84          = (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3)))
% 1.67/1.84        | ~ (v1_relat_1 @ sk_C_2)
% 1.67/1.84        | ~ (v1_funct_1 @ sk_C_2))),
% 1.67/1.84      inference('sup+', [status(thm)], ['50', '56'])).
% 1.67/1.84  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('59', plain, ((v1_funct_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('60', plain,
% 1.67/1.84      (((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84         = (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3)))),
% 1.67/1.84      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.67/1.84  thf('61', plain,
% 1.67/1.84      ((r2_hidden @ 
% 1.67/1.84        (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ 
% 1.67/1.84         (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))) @ 
% 1.67/1.84        sk_D_3)),
% 1.67/1.84      inference('demod', [status(thm)], ['27', '60'])).
% 1.67/1.84  thf('62', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X0)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X1))),
% 1.67/1.84      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.67/1.84  thf('63', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.84         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.67/1.84          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | ~ (v1_relat_1 @ X16))),
% 1.67/1.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.67/1.84  thf('64', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X0) = (X1))
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0))))),
% 1.67/1.84      inference('sup-', [status(thm)], ['62', '63'])).
% 1.67/1.84  thf('65', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (((sk_D @ X1 @ X0) = (k1_funct_1 @ X0 @ (sk_C @ X1 @ X0)))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ~ (v1_relat_1 @ X1)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 1.67/1.84          | ((X0) = (X1))
% 1.67/1.84          | ~ (v1_relat_1 @ X0))),
% 1.67/1.84      inference('simplify', [status(thm)], ['64'])).
% 1.67/1.84  thf('66', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.67/1.84         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 1.67/1.84          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | ~ (v1_relat_1 @ X16))),
% 1.67/1.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.67/1.84  thf('67', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X1)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X1)
% 1.67/1.84          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1))))),
% 1.67/1.84      inference('sup-', [status(thm)], ['65', '66'])).
% 1.67/1.84  thf('68', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (((sk_D @ X0 @ X1) = (k1_funct_1 @ X0 @ (sk_C @ X0 @ X1)))
% 1.67/1.84          | ~ (v1_funct_1 @ X0)
% 1.67/1.84          | ((sk_D @ X0 @ X1) = (k1_funct_1 @ X1 @ (sk_C @ X0 @ X1)))
% 1.67/1.84          | ~ (v1_funct_1 @ X1)
% 1.67/1.84          | ~ (v1_relat_1 @ X0)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X1))),
% 1.67/1.84      inference('simplify', [status(thm)], ['67'])).
% 1.67/1.84  thf('69', plain,
% 1.67/1.84      (((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84         = (k1_funct_1 @ sk_D_3 @ (sk_C @ sk_C_2 @ sk_D_3)))),
% 1.67/1.84      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.67/1.84  thf('70', plain,
% 1.67/1.84      ((((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84          = (sk_D @ sk_C_2 @ sk_D_3))
% 1.67/1.84        | ~ (v1_relat_1 @ sk_D_3)
% 1.67/1.84        | ((sk_D_3) = (sk_C_2))
% 1.67/1.84        | ~ (v1_relat_1 @ sk_C_2)
% 1.67/1.84        | ~ (v1_funct_1 @ sk_D_3)
% 1.67/1.84        | ~ (v1_funct_1 @ sk_C_2)
% 1.67/1.84        | ((sk_D @ sk_C_2 @ sk_D_3)
% 1.67/1.84            = (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))))),
% 1.67/1.84      inference('sup+', [status(thm)], ['68', '69'])).
% 1.67/1.84  thf('71', plain, ((v1_relat_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('73', plain, ((v1_funct_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('74', plain, ((v1_funct_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('75', plain,
% 1.67/1.84      ((((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84          = (sk_D @ sk_C_2 @ sk_D_3))
% 1.67/1.84        | ((sk_D_3) = (sk_C_2))
% 1.67/1.84        | ((sk_D @ sk_C_2 @ sk_D_3)
% 1.67/1.84            = (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))))),
% 1.67/1.84      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 1.67/1.84  thf('76', plain,
% 1.67/1.84      ((((sk_D_3) = (sk_C_2))
% 1.67/1.84        | ((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84            = (sk_D @ sk_C_2 @ sk_D_3)))),
% 1.67/1.84      inference('simplify', [status(thm)], ['75'])).
% 1.67/1.84  thf('77', plain, (((sk_C_2) != (sk_D_3))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('78', plain,
% 1.67/1.84      (((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84         = (sk_D @ sk_C_2 @ sk_D_3))),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.67/1.84  thf('79', plain,
% 1.67/1.84      ((r2_hidden @ 
% 1.67/1.84        (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ (sk_D @ sk_C_2 @ sk_D_3)) @ 
% 1.67/1.84        sk_D_3)),
% 1.67/1.84      inference('demod', [status(thm)], ['61', '78'])).
% 1.67/1.84  thf('80', plain,
% 1.67/1.84      (![X0 : $i, X1 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X0)
% 1.67/1.84          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.67/1.84               X1)
% 1.67/1.84          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ 
% 1.67/1.84               X0)
% 1.67/1.84          | ((X1) = (X0))
% 1.67/1.84          | ~ (v1_relat_1 @ X1))),
% 1.67/1.84      inference('cnf', [status(esa)], [d2_relat_1])).
% 1.67/1.84  thf('81', plain,
% 1.67/1.84      ((~ (v1_relat_1 @ sk_D_3)
% 1.67/1.84        | ((sk_D_3) = (sk_C_2))
% 1.67/1.84        | ~ (r2_hidden @ 
% 1.67/1.84             (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ (sk_D @ sk_C_2 @ sk_D_3)) @ 
% 1.67/1.84             sk_C_2)
% 1.67/1.84        | ~ (v1_relat_1 @ sk_C_2))),
% 1.67/1.84      inference('sup-', [status(thm)], ['79', '80'])).
% 1.67/1.84  thf('82', plain, ((v1_relat_1 @ sk_D_3)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('83', plain, ((r2_hidden @ (sk_C @ sk_C_2 @ sk_D_3) @ sk_A)),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 1.67/1.84  thf('84', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('85', plain,
% 1.67/1.84      (![X15 : $i, X16 : $i]:
% 1.67/1.84         (~ (v1_relat_1 @ X16)
% 1.67/1.84          | ~ (v1_funct_1 @ X16)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X15 @ (k1_funct_1 @ X16 @ X15)) @ X16)
% 1.67/1.84          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X16)))),
% 1.67/1.84      inference('simplify', [status(thm)], ['21'])).
% 1.67/1.84  thf('86', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2)
% 1.67/1.84          | ~ (v1_funct_1 @ sk_C_2)
% 1.67/1.84          | ~ (v1_relat_1 @ sk_C_2))),
% 1.67/1.84      inference('sup-', [status(thm)], ['84', '85'])).
% 1.67/1.84  thf('87', plain, ((v1_funct_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('88', plain, ((v1_relat_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('89', plain,
% 1.67/1.84      (![X0 : $i]:
% 1.67/1.84         (~ (r2_hidden @ X0 @ sk_A)
% 1.67/1.84          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2))),
% 1.67/1.84      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.67/1.84  thf('90', plain,
% 1.67/1.84      ((r2_hidden @ 
% 1.67/1.84        (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ 
% 1.67/1.84         (k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))) @ 
% 1.67/1.84        sk_C_2)),
% 1.67/1.84      inference('sup-', [status(thm)], ['83', '89'])).
% 1.67/1.84  thf('91', plain,
% 1.67/1.84      (((k1_funct_1 @ sk_C_2 @ (sk_C @ sk_C_2 @ sk_D_3))
% 1.67/1.84         = (sk_D @ sk_C_2 @ sk_D_3))),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.67/1.84  thf('92', plain,
% 1.67/1.84      ((r2_hidden @ 
% 1.67/1.84        (k4_tarski @ (sk_C @ sk_C_2 @ sk_D_3) @ (sk_D @ sk_C_2 @ sk_D_3)) @ 
% 1.67/1.84        sk_C_2)),
% 1.67/1.84      inference('demod', [status(thm)], ['90', '91'])).
% 1.67/1.84  thf('93', plain, ((v1_relat_1 @ sk_C_2)),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('94', plain, (((sk_D_3) = (sk_C_2))),
% 1.67/1.84      inference('demod', [status(thm)], ['81', '82', '92', '93'])).
% 1.67/1.84  thf('95', plain, (((sk_C_2) != (sk_D_3))),
% 1.67/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.67/1.84  thf('96', plain, ($false),
% 1.67/1.84      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.67/1.84  
% 1.67/1.84  % SZS output end Refutation
% 1.67/1.84  
% 1.67/1.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
