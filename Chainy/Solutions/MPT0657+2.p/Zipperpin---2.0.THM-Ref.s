%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0657+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V7xcv6U6YL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 27.80s
% Output     : Refutation 27.80s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 409 expanded)
%              Number of leaves         :   24 ( 132 expanded)
%              Depth                    :   18
%              Number of atoms          :  655 (6099 expanded)
%              Number of equality atoms :   64 ( 667 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_24_type,type,(
    sk_B_24: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t64_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ ( B @ A ) )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v2_funct_1 @ A )
                & ( ( k2_relat_1 @ B )
                  = ( k1_relat_1 @ A ) )
                & ( ( k5_relat_1 @ ( B @ A ) )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('0',plain,(
    sk_B_24
 != ( k2_funct_1 @ sk_A_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ ( A @ ( k2_relat_1 @ A ) ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2355: $i] :
      ( ( ( k10_relat_1 @ ( X2355 @ ( k2_relat_1 @ X2355 ) ) )
        = ( k1_relat_1 @ X2355 ) )
      | ~ ( v1_relat_1 @ X2355 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('2',plain,
    ( ( k5_relat_1 @ ( sk_B_24 @ sk_A_8 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( k5_relat_1 @ ( sk_B_24 @ sk_A_8 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('5',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_B_24 @ sk_A_8 ) ) )
    = ( k2_relat_1 @ sk_A_8 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
            = ( k10_relat_1 @ ( A @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X2386: $i,X2387: $i] :
      ( ~ ( v1_relat_1 @ X2386 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( X2387 @ X2386 ) ) )
        = ( k10_relat_1 @ ( X2387 @ ( k1_relat_1 @ X2386 ) ) ) )
      | ~ ( v1_relat_1 @ X2387 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_A_8 )
      = ( k10_relat_1 @ ( sk_B_24 @ ( k1_relat_1 @ sk_A_8 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_relat_1 @ sk_A_8 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relat_1 @ sk_B_24 )
    = ( k1_relat_1 @ sk_A_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_A_8 )
    = ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ( k5_relat_1 @ ( sk_B_24 @ sk_A_8 ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) ) ),
    inference(demod,[status(thm)],['2','11'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ ( A @ B ) )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X2825: $i,X2826: $i] :
      ( ~ ( v1_relat_1 @ X2825 )
      | ~ ( v1_funct_1 @ X2825 )
      | ( X2825
        = ( k2_funct_1 @ X2826 ) )
      | ( ( k5_relat_1 @ ( X2826 @ X2825 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X2826 ) ) )
      | ( ( k2_relat_1 @ X2826 )
       != ( k1_relat_1 @ X2825 ) )
      | ~ ( v2_funct_1 @ X2826 )
      | ~ ( v1_funct_1 @ X2826 )
      | ~ ( v1_relat_1 @ X2826 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('14',plain,
    ( ( ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ sk_B_24 )
    | ( ( k2_relat_1 @ sk_B_24 )
     != ( k1_relat_1 @ sk_A_8 ) )
    | ( sk_A_8
      = ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_funct_1 @ sk_A_8 )
    | ~ ( v1_relat_1 @ sk_A_8 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k5_relat_1 @ ( sk_B_24 @ sk_A_8 ) )
    = ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) ) ),
    inference(demod,[status(thm)],['2','11'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ ( B @ A ) ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X2777: $i,X2778: $i] :
      ( ~ ( v1_relat_1 @ X2777 )
      | ~ ( v1_funct_1 @ X2777 )
      | ( v2_funct_1 @ X2777 )
      | ( ( k2_relat_1 @ X2777 )
       != ( k1_relat_1 @ X2778 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( X2777 @ X2778 ) ) )
      | ~ ( v1_funct_1 @ X2778 )
      | ~ ( v1_relat_1 @ X2778 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('19',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_A_8 )
    | ~ ( v1_funct_1 @ sk_A_8 )
    | ( ( k2_relat_1 @ sk_B_24 )
     != ( k1_relat_1 @ sk_A_8 ) )
    | ( v2_funct_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X2651: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2651 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('21',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_B_24 )
    = ( k1_relat_1 @ sk_A_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_B_24 )
     != ( k2_relat_1 @ sk_B_24 ) )
    | ( v2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_B_24 )
    = ( k1_relat_1 @ sk_A_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_A_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ( ( k2_relat_1 @ sk_B_24 )
     != ( k2_relat_1 @ sk_B_24 ) )
    | ( sk_A_8
      = ( k2_funct_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['14','15','16','27','28','29','30'])).

thf('32',plain,
    ( ( sk_A_8
      = ( k2_funct_1 @ sk_B_24 ) )
    | ( ( k6_relat_1 @ ( k10_relat_1 @ ( sk_B_24 @ ( k2_relat_1 @ sk_B_24 ) ) ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ( sk_A_8
      = ( k2_funct_1 @ sk_B_24 ) ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ( sk_A_8
      = ( k2_funct_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A_8
    = ( k2_funct_1 @ sk_B_24 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X2653: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2653 ) )
      | ~ ( v2_funct_1 @ X2653 )
      | ~ ( v1_funct_1 @ X2653 )
      | ~ ( v1_relat_1 @ X2653 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('38',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X2632: $i] :
      ( ~ ( v2_funct_1 @ X2632 )
      | ( ( k2_funct_1 @ X2632 )
        = ( k4_relat_1 @ X2632 ) )
      | ~ ( v1_funct_1 @ X2632 )
      | ~ ( v1_relat_1 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_B_24 )
    | ( ( k2_funct_1 @ sk_B_24 )
      = ( k4_relat_1 @ sk_B_24 ) )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_funct_1 @ sk_B_24 )
      = ( k4_relat_1 @ sk_B_24 ) )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(simplify,[status(thm)],['26'])).

thf('44',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X2132: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2132 ) )
      | ~ ( v1_relat_1 @ X2132 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('46',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2632: $i] :
      ( ~ ( v2_funct_1 @ X2632 )
      | ( ( k2_funct_1 @ X2632 )
        = ( k4_relat_1 @ X2632 ) )
      | ~ ( v1_funct_1 @ X2632 )
      | ~ ( v1_relat_1 @ X2632 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_B_24 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(fc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k4_relat_1 @ A ) )
        & ( v1_funct_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X2652: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X2652 ) )
      | ~ ( v2_funct_1 @ X2652 )
      | ~ ( v1_funct_1 @ X2652 )
      | ~ ( v1_relat_1 @ X2652 ) ) ),
    inference(cnf,[status(esa)],[fc5_funct_1])).

thf('53',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(simplify,[status(thm)],['26'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_B_24 )
    = ( k4_relat_1 @ sk_B_24 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X2186: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X2186 ) )
        = X2186 )
      | ~ ( v1_relat_1 @ X2186 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('60',plain,
    ( ( ( k4_relat_1 @ ( k2_funct_1 @ sk_B_24 ) )
      = sk_B_24 )
    | ~ ( v1_relat_1 @ sk_B_24 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k4_relat_1 @ ( k2_funct_1 @ sk_B_24 ) )
    = sk_B_24 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
      = sk_B_24 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) ) ),
    inference(demod,[status(thm)],['50','57','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ sk_B_24 )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
      = sk_B_24 ) ),
    inference('sup-',[status(thm)],['37','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_B_24 ),
    inference(simplify,[status(thm)],['26'])).

thf('68',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_B_24 ) )
    = sk_B_24 ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    sk_B_24 != sk_B_24 ),
    inference(demod,[status(thm)],['0','36','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
