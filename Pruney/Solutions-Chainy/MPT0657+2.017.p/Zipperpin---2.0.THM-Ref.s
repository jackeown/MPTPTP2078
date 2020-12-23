%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXJuB7Tj4u

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 194 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  538 (2781 expanded)
%              Number of equality atoms :   62 ( 317 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
              & ( ( k5_relat_1 @ B @ A )
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
                & ( ( k5_relat_1 @ B @ A )
                  = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
             => ( B
                = ( k2_funct_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_1])).

thf('0',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('2',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X1 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_B @ sk_A ) )
    = ( k2_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k10_relat_1 @ X3 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k10_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

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
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_B @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_B ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_B @ X0 )
       != ( k5_relat_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','32','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( sk_A
      = ( k4_relat_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A
      = ( k4_relat_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( sk_A
    = ( k4_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k4_relat_1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['2','46'])).

thf('48',plain,(
    sk_B
 != ( k2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    sk_B
 != ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GXJuB7Tj4u
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 44 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(t64_funct_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.48               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.21/0.48               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.21/0.48             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48              ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.48                  ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.21/0.48                  ( ( k5_relat_1 @ B @ A ) =
% 0.21/0.48                    ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.21/0.48                ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t64_funct_1])).
% 0.21/0.48  thf('0', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(involutiveness_k4_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k4_relat_1 @ (k4_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.21/0.48  thf('2', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_B)) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t169_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X1 : $i]:
% 0.21/0.48         (((k10_relat_1 @ X1 @ (k2_relat_1 @ X1)) = (k1_relat_1 @ X1))
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t71_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('5', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((k1_relat_1 @ (k5_relat_1 @ sk_B @ sk_A)) = (k2_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(t182_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v1_relat_1 @ B ) =>
% 0.21/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X2)
% 0.21/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2))
% 0.21/0.48              = (k10_relat_1 @ X3 @ (k1_relat_1 @ X2)))
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A) = (k10_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((k2_relat_1 @ sk_A) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B)) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '12'])).
% 0.21/0.48  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf(t63_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48           ( ( ( v2_funct_1 @ A ) & 
% 0.21/0.48               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.21/0.48               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.21/0.48             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X9)
% 0.21/0.48          | ~ (v1_funct_1 @ X9)
% 0.21/0.48          | ((X9) = (k2_funct_1 @ X10))
% 0.21/0.48          | ((k5_relat_1 @ X10 @ X9) != (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.21/0.48          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X9))
% 0.21/0.48          | ~ (v2_funct_1 @ X10)
% 0.21/0.48          | ~ (v1_funct_1 @ X10)
% 0.21/0.48          | ~ (v1_relat_1 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k5_relat_1 @ sk_B @ X0) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.48          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.48          | ~ (v2_funct_1 @ sk_B)
% 0.21/0.48          | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.21/0.48          | ((X0) = (k2_funct_1 @ sk_B))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k5_relat_1 @ sk_B @ X0) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.48          | ~ (v2_funct_1 @ sk_B)
% 0.21/0.48          | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.21/0.48          | ((X0) = (k2_funct_1 @ sk_B))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.21/0.48  thf('22', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf(t53_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( ?[B:$i]:
% 0.21/0.48           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.48             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.21/0.48         ( v2_funct_1 @ A ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X7)
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.21/0.48          | (v2_funct_1 @ X8)
% 0.21/0.48          | ~ (v1_funct_1 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k5_relat_1 @ sk_B @ X0) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))
% 0.21/0.48          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.48          | (v2_funct_1 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((k5_relat_1 @ sk_B @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k5_relat_1 @ sk_B @ X0) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.48          | (v2_funct_1 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | (v2_funct_1 @ sk_B))),
% 0.21/0.48      inference('eq_res', [status(thm)], ['28'])).
% 0.21/0.48  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.48  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d9_funct_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X6)
% 0.21/0.48          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.21/0.48          | ~ (v1_funct_1 @ X6)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.48        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 0.21/0.48        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B)) | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.48  thf('39', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k5_relat_1 @ sk_B @ X0) != (k5_relat_1 @ sk_B @ sk_A))
% 0.21/0.48          | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ X0))
% 0.21/0.48          | ((X0) = (k4_relat_1 @ sk_B))
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '32', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ((sk_A) = (k4_relat_1 @ sk_B))
% 0.21/0.48        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_A)))),
% 0.21/0.48      inference('eq_res', [status(thm)], ['40'])).
% 0.21/0.48  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain, (((k2_relat_1 @ sk_B) = (k1_relat_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((((sk_A) = (k4_relat_1 @ sk_B))
% 0.21/0.48        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.21/0.48  thf('46', plain, (((sk_A) = (k4_relat_1 @ sk_B))),
% 0.21/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.48  thf('47', plain, (((k4_relat_1 @ sk_A) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '46'])).
% 0.21/0.48  thf('48', plain, (((sk_B) != (k2_funct_1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X6)
% 0.21/0.48          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.21/0.48          | ~ (v1_funct_1 @ X6)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((~ (v1_funct_1 @ sk_A)
% 0.21/0.48        | ((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))
% 0.21/0.48        | ~ (v2_funct_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('53', plain, ((v2_funct_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('54', plain, (((k2_funct_1 @ sk_A) = (k4_relat_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.48  thf('55', plain, (((sk_B) != (k4_relat_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '54'])).
% 0.21/0.48  thf('56', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['47', '55'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
