%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rX4VFx8v74

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  503 ( 727 expanded)
%              Number of equality atoms :   53 (  71 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( m1_subset_1 @ ( sk_B @ X16 ) @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_tarski @ X13 )
       != ( k2_xboole_0 @ X11 @ X12 ) )
      | ( zip_tseitin_2 @ X12 @ X11 @ X13 )
      | ( zip_tseitin_1 @ X12 @ X11 @ X13 )
      | ( zip_tseitin_0 @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
       != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,
    ( ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k1_tarski @ X8 ) )
      | ~ ( zip_tseitin_2 @ X10 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X6 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3
        = ( k1_tarski @ X2 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_B_1 = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B_1 = sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rX4VFx8v74
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 27 iterations in 0.019s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(t1_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.48              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.20/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.48         ( ?[B:$i]:
% 0.20/0.48           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.48          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.20/0.48          | (v1_xboole_0 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.48          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.20/0.48          | (v1_xboole_0 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X14)
% 0.20/0.48          | ~ (m1_subset_1 @ X15 @ X14)
% 0.20/0.48          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.48          | (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t12_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('8', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t43_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.48          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_2, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_4, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.48       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_6, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_7, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.48          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (((k1_tarski @ X13) != (k2_xboole_0 @ X11 @ X12))
% 0.20/0.48          | (zip_tseitin_2 @ X12 @ X11 @ X13)
% 0.20/0.48          | (zip_tseitin_1 @ X12 @ X11 @ X13)
% 0.20/0.48          | (zip_tseitin_0 @ X12 @ X11 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_tarski @ X0) != (sk_B_1))
% 0.20/0.48          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ X0)
% 0.20/0.48          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ X0)
% 0.20/0.48          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_domain_1 @ X0 @ (sk_B @ X0)) != (sk_B_1))
% 0.20/0.48          | (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.48          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.48          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) != (sk_B_1))
% 0.20/0.48          | (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.48          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.48          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (((X9) = (k1_tarski @ X8)) | ~ (zip_tseitin_2 @ X10 @ X9 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.48        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (((X5) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X6 @ X5 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.48        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (((X3) = (k1_tarski @ X2)) | ~ (zip_tseitin_0 @ X4 @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.48        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.48        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('23', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ X16)
% 0.20/0.48          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.20/0.48          | (v1_xboole_0 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.48          | (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ X0)
% 0.20/0.48          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((sk_B_1) = (sk_A))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.48        | ~ (v1_zfmisc_1 @ sk_B_1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '28'])).
% 0.20/0.48  thf('30', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((sk_B_1) = (sk_A)) | ((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.48  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf('37', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '35', '36'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
