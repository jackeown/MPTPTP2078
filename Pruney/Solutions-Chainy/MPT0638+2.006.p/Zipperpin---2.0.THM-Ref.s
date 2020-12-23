%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ze8c3XrVRQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 189 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  601 (2781 expanded)
%              Number of equality atoms :   48 ( 317 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t44_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( ( k2_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
                & ( ( k5_relat_1 @ A @ B )
                  = A ) )
             => ( B
                = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_funct_1])).

thf('0',plain,
    ( ( k5_relat_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
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

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    sk_B
 != ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['13','15'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

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

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['13','15'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','32'])).

thf('34',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ X10 ) )
       != ( sk_C_1 @ X11 @ X10 ) )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('40',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('48',plain,(
    ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ze8c3XrVRQ
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 61 iterations in 0.075s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(t44_funct_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.52               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.20/0.52             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52              ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.20/0.52                  ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.20/0.52                ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t44_funct_1])).
% 0.20/0.52  thf('0', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t34_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.52         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X11) != (X10))
% 0.20/0.52          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 0.20/0.52          | ((X11) = (k6_relat_1 @ X10))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X11)
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.20/0.52          | (r2_hidden @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)) @ 
% 0.20/0.52             (k1_relat_1 @ X11)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.20/0.52         (k1_relat_1 @ sk_B))
% 0.20/0.52        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['1', '3'])).
% 0.20/0.52  thf('5', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.20/0.52         (k2_relat_1 @ sk_A))
% 0.20/0.52        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.20/0.52  thf('10', plain, (((sk_B) != (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.20/0.52  thf(d5_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.52          | ((X3) != (k2_relat_1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X2 : $i, X4 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.20/0.52         (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.20/0.52        sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.52  thf(t8_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.20/0.52          | (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (v1_relat_1 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.20/0.52           (k1_relat_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.20/0.52        (k1_relat_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.52  thf(t23_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.52           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.52             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.52               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X7)
% 0.20/0.52          | ~ (v1_funct_1 @ X7)
% 0.20/0.52          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.52              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.52          | ~ (v1_funct_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ sk_A)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_A)
% 0.20/0.52          | ((k1_funct_1 @ (k5_relat_1 @ sk_A @ X0) @ 
% 0.20/0.52              (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.20/0.52              = (k1_funct_1 @ X0 @ 
% 0.20/0.52                 (k1_funct_1 @ sk_A @ 
% 0.20/0.52                  (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k4_tarski @ (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.20/0.52         (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))) @ 
% 0.20/0.52        sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.20/0.52          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.20/0.52          | ~ (v1_funct_1 @ X14)
% 0.20/0.52          | ~ (v1_relat_1 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_A)
% 0.20/0.52        | ((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.20/0.52            = (k1_funct_1 @ sk_A @ 
% 0.20/0.52               (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.20/0.52         = (k1_funct_1 @ sk_A @ 
% 0.20/0.52            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_funct_1 @ (k5_relat_1 @ sk_A @ X0) @ 
% 0.20/0.52            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.20/0.52            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))
% 0.20/0.52          | ~ (v1_funct_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24', '25', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((k1_funct_1 @ sk_A @ 
% 0.20/0.52          (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.20/0.52          = (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['0', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.20/0.52         = (k1_funct_1 @ sk_A @ 
% 0.20/0.52            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.20/0.52         = (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.20/0.52  thf('38', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X11) != (X10))
% 0.20/0.52          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ X10)) != (sk_C_1 @ X11 @ X10))
% 0.20/0.52          | ((X11) = (k6_relat_1 @ X10))
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X11)
% 0.20/0.52          | ~ (v1_funct_1 @ X11)
% 0.20/0.52          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.20/0.52          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)))
% 0.20/0.52              != (sk_C_1 @ X11 @ (k1_relat_1 @ X11))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.52          != (sk_C_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.20/0.52        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.20/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '40'])).
% 0.20/0.52  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.52          != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.52        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.20/0.52  thf('47', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.20/0.52         != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['37', '48'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
