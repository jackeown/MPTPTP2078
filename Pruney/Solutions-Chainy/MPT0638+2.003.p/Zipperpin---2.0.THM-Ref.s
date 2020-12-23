%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNuMphcswA

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:10 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 179 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  584 (2693 expanded)
%              Number of equality atoms :   50 ( 319 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf('14',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('15',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

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

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k1_funct_1 @ X7 @ ( k1_funct_1 @ X8 @ X9 ) ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ ( k2_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf('25',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('26',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_A @ X0 ) @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
        = ( k1_funct_1 @ X0 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','30'])).

thf('32',plain,
    ( ( ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','31'])).

thf('33',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_A @ ( sk_D_1 @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C_1 @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
     != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
    | ( sk_B
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    sk_B
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('47',plain,(
    ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) )
 != ( sk_C_1 @ sk_B @ ( k2_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNuMphcswA
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 139 iterations in 0.177s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.63  thf(t44_funct_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.46/0.63               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.46/0.63             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63              ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.46/0.63                  ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 0.46/0.63                ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t44_funct_1])).
% 0.46/0.63  thf('0', plain, (((k5_relat_1 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t34_funct_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.46/0.63         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         (((k1_relat_1 @ X11) != (X10))
% 0.46/0.63          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 0.46/0.63          | ((X11) = (k6_relat_1 @ X10))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_relat_1 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X11)
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.46/0.63          | (r2_hidden @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)) @ 
% 0.46/0.63             (k1_relat_1 @ X11)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.46/0.63         (k1_relat_1 @ sk_B))
% 0.46/0.63        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['1', '3'])).
% 0.46/0.63  thf('5', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ 
% 0.46/0.63         (k2_relat_1 @ sk_A))
% 0.46/0.63        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.46/0.63  thf('10', plain, (((sk_B) != (k6_relat_1 @ (k1_relat_1 @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('11', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('12', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.46/0.63  thf(d5_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.63               ( ?[D:$i]:
% 0.46/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         (((X3) != (k2_relat_1 @ X1))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1))
% 0.46/0.63          | ~ (r2_hidden @ X4 @ X3)
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X1 : $i, X4 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.46/0.63          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63         (k1_relat_1 @ sk_A))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['13', '15'])).
% 0.46/0.63  thf('17', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A) @ 
% 0.46/0.63        (k1_relat_1 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.46/0.63  thf(t23_funct_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.63           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.63             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.46/0.63               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X7)
% 0.46/0.63          | ~ (v1_funct_1 @ X7)
% 0.46/0.63          | ((k1_funct_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.46/0.63              = (k1_funct_1 @ X7 @ (k1_funct_1 @ X8 @ X9)))
% 0.46/0.63          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.46/0.63          | ~ (v1_funct_1 @ X8)
% 0.46/0.63          | ~ (v1_relat_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ sk_A)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63          | ((k1_funct_1 @ (k5_relat_1 @ sk_A @ X0) @ 
% 0.46/0.63              (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.46/0.63              = (k1_funct_1 @ X0 @ 
% 0.46/0.63                 (k1_funct_1 @ sk_A @ 
% 0.46/0.63                  (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.63  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('23', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((r2_hidden @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ (k2_relat_1 @ sk_A))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         (((X3) != (k2_relat_1 @ X1))
% 0.46/0.63          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1)))
% 0.46/0.63          | ~ (r2_hidden @ X4 @ X3)
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X1 : $i, X4 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_funct_1 @ X1)
% 0.46/0.63          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.46/0.63          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['25'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      ((((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.63          = (k1_funct_1 @ sk_A @ 
% 0.46/0.63             (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['24', '26'])).
% 0.46/0.63  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.64         = (k1_funct_1 @ sk_A @ 
% 0.46/0.64            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_funct_1 @ (k5_relat_1 @ sk_A @ X0) @ 
% 0.46/0.64            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.46/0.64            = (k1_funct_1 @ X0 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['21', '22', '23', '30'])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((((k1_funct_1 @ sk_A @ 
% 0.46/0.64          (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A))
% 0.46/0.64          = (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['0', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.64         = (k1_funct_1 @ sk_A @ 
% 0.46/0.64            (sk_D_1 @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)) @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.64  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))
% 0.46/0.64         = (k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.46/0.64  thf('37', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         (((k1_relat_1 @ X11) != (X10))
% 0.46/0.64          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ X10)) != (sk_C_1 @ X11 @ X10))
% 0.46/0.64          | ((X11) = (k6_relat_1 @ X10))
% 0.46/0.64          | ~ (v1_funct_1 @ X11)
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X11 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X11)
% 0.46/0.64          | ~ (v1_funct_1 @ X11)
% 0.46/0.64          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.46/0.64          | ((k1_funct_1 @ X11 @ (sk_C_1 @ X11 @ (k1_relat_1 @ X11)))
% 0.46/0.64              != (sk_C_1 @ X11 @ (k1_relat_1 @ X11))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.64          != (sk_C_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.46/0.64        | ((sk_B) = (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_B)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '39'])).
% 0.46/0.64  thf('41', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('42', plain, (((k2_relat_1 @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.64          != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.64        | ((sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.46/0.64  thf('46', plain, (((sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))
% 0.46/0.64         != (sk_C_1 @ sk_B @ (k2_relat_1 @ sk_A)))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['36', '47'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
