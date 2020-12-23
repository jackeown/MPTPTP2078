%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FpBOunWKp

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:15 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 173 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  752 (3262 expanded)
%              Number of equality atoms :   70 ( 394 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != X9 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 )
      | ( X10
        = ( k6_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ ( k1_relat_1 @ X10 ) ) @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k1_funct_1 @ X6 @ ( k1_funct_1 @ X7 @ X8 ) ) )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) ) ) )
    | ( sk_C_2
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) ) )
    | ( sk_C_2
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10','11','12','13'])).

thf('15',plain,(
    sk_C_2
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
    = ( k1_funct_1 @ sk_B_1 @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
        = X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ ( k1_relat_1 @ X10 ) ) @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A )
    | ( sk_C_2
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    sk_C_2
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X5 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X3 @ X4 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['25','46'])).

thf('48',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
      = ( sk_C_1 @ sk_C_2 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
    = ( sk_C_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ X10 )
       != X9 )
      | ( ( k1_funct_1 @ X10 @ ( sk_C_1 @ X10 @ X9 ) )
       != ( sk_C_1 @ X10 @ X9 ) )
      | ( X10
        = ( k6_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('53',plain,(
    ! [X10: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k1_funct_1 @ X10 @ ( sk_C_1 @ X10 @ ( k1_relat_1 @ X10 ) ) )
       != ( sk_C_1 @ X10 @ ( k1_relat_1 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
     != ( sk_C_1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ( sk_C_2
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
     != ( sk_C_1 @ sk_C_2 @ sk_A ) )
    | ( sk_C_2
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    sk_C_2
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_A ) )
 != ( sk_C_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FpBOunWKp
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 201 iterations in 0.153s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.42/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.42/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.42/0.62  thf(t50_funct_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.42/0.62               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.42/0.62               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.42/0.62               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.42/0.62             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62          ( ![C:$i]:
% 0.42/0.62            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.42/0.62                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.42/0.62                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.42/0.62                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.42/0.62                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.42/0.62  thf('0', plain, (((k5_relat_1 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t34_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.42/0.62         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X10) != (X9))
% 0.42/0.62          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9)
% 0.42/0.62          | ((X10) = (k6_relat_1 @ X9))
% 0.42/0.62          | ~ (v1_funct_1 @ X10)
% 0.42/0.62          | ~ (v1_relat_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X10 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X10)
% 0.42/0.62          | ~ (v1_funct_1 @ X10)
% 0.42/0.62          | ((X10) = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.42/0.62          | (r2_hidden @ (sk_C_1 @ X10 @ (k1_relat_1 @ X10)) @ 
% 0.42/0.62             (k1_relat_1 @ X10)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.62  thf(t23_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.42/0.62             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.42/0.62               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X6)
% 0.42/0.62          | ~ (v1_funct_1 @ X6)
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 0.42/0.62              = (k1_funct_1 @ X6 @ (k1_funct_1 @ X7 @ X8)))
% 0.42/0.62          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.42/0.62          | ~ (v1_funct_1 @ X7)
% 0.42/0.62          | ~ (v1_relat_1 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.42/0.62              (sk_C_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.42/0.62              = (k1_funct_1 @ X1 @ 
% 0.42/0.62                 (k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ (k1_relat_1 @ X0)))))
% 0.42/0.62          | ~ (v1_funct_1 @ X1)
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X1)
% 0.42/0.62          | ~ (v1_funct_1 @ X1)
% 0.42/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.42/0.62              (sk_C_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.42/0.62              = (k1_funct_1 @ X1 @ 
% 0.42/0.62                 (k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ (k1_relat_1 @ X0)))))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((X0) = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))
% 0.42/0.62          = (k1_funct_1 @ sk_B_1 @ 
% 0.42/0.62             (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))))
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ (k1_relat_1 @ sk_C_2)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C_2)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C_2)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_B_1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['0', '5'])).
% 0.42/0.62  thf('7', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('8', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('10', plain, ((v1_funct_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('11', plain, ((v1_relat_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62          = (k1_funct_1 @ sk_B_1 @ 
% 0.42/0.62             (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))))
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)],
% 0.42/0.62                ['6', '7', '8', '9', '10', '11', '12', '13'])).
% 0.42/0.62  thf('15', plain, (((sk_C_2) != (k6_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62         = (k1_funct_1 @ sk_B_1 @ 
% 0.42/0.62            (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d8_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ( v2_funct_1 @ A ) <=>
% 0.42/0.62         ( ![B:$i,C:$i]:
% 0.42/0.62           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.42/0.62             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.42/0.62          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.42/0.62          | ((X1) = (X2))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v2_funct_1 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('20', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('21', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('22', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('23', plain, ((v2_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | ((X0) = (X1))
% 0.42/0.62          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) = (X0))
% 0.42/0.62          | ~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) @ 
% 0.42/0.62               sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '24'])).
% 0.42/0.62  thf('26', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X10 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X10)
% 0.42/0.62          | ~ (v1_funct_1 @ X10)
% 0.42/0.62          | ((X10) = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.42/0.62          | (r2_hidden @ (sk_C_1 @ X10 @ (k1_relat_1 @ X10)) @ 
% 0.42/0.62             (k1_relat_1 @ X10)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ (k1_relat_1 @ sk_C_2))
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ (k1_relat_1 @ sk_C_2)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C_2)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C_2))),
% 0.42/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('30', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('31', plain, ((v1_funct_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('32', plain, ((v1_relat_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.42/0.62  thf('34', plain, (((sk_C_2) != (k6_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('35', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain, (((k5_relat_1 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t21_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.42/0.62             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.42/0.62               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X3)
% 0.42/0.62          | ~ (v1_funct_1 @ X3)
% 0.42/0.62          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ (k5_relat_1 @ X3 @ X5)))
% 0.42/0.62          | (r2_hidden @ (k1_funct_1 @ X3 @ X4) @ (k1_relat_1 @ X5))
% 0.42/0.62          | ~ (v1_funct_1 @ X5)
% 0.42/0.62          | ~ (v1_relat_1 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k1_relat_1 @ sk_B_1))
% 0.42/0.62          | ~ (v1_funct_1 @ sk_C_2)
% 0.42/0.62          | ~ (v1_relat_1 @ sk_C_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain, ((v1_relat_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain, ((v1_funct_1 @ sk_B_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('42', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('43', plain, ((v1_funct_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('44', plain, ((v1_relat_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)],
% 0.42/0.62                ['38', '39', '40', '41', '42', '43', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '45'])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_funct_1 @ sk_B_1 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62            != (k1_funct_1 @ sk_B_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A)) = (X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['25', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62          = (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62        | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A))),
% 0.42/0.62      inference('eq_res', [status(thm)], ['47'])).
% 0.42/0.62  thf('49', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_A) @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62         = (sk_C_1 @ sk_C_2 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('51', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X10) != (X9))
% 0.42/0.62          | ((k1_funct_1 @ X10 @ (sk_C_1 @ X10 @ X9)) != (sk_C_1 @ X10 @ X9))
% 0.42/0.62          | ((X10) = (k6_relat_1 @ X9))
% 0.42/0.62          | ~ (v1_funct_1 @ X10)
% 0.42/0.62          | ~ (v1_relat_1 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X10 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X10)
% 0.42/0.62          | ~ (v1_funct_1 @ X10)
% 0.42/0.62          | ((X10) = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.42/0.62          | ((k1_funct_1 @ X10 @ (sk_C_1 @ X10 @ (k1_relat_1 @ X10)))
% 0.42/0.62              != (sk_C_1 @ X10 @ (k1_relat_1 @ X10))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62          != (sk_C_1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2)))
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ (k1_relat_1 @ sk_C_2)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C_2)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C_2))),
% 0.42/0.62      inference('sup-', [status(thm)], ['51', '53'])).
% 0.42/0.62  thf('55', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('56', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('57', plain, ((v1_funct_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62          != (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62        | ((sk_C_2) = (k6_relat_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.42/0.62  thf('60', plain, (((sk_C_2) != (k6_relat_1 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_A))
% 0.42/0.62         != (sk_C_1 @ sk_C_2 @ sk_A))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.42/0.62  thf('62', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['50', '61'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
