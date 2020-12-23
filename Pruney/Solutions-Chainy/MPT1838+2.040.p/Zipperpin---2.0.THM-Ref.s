%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uECGlv4LIW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 101 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   20
%              Number of atoms          :  533 ( 801 expanded)
%              Number of equality atoms :   59 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ~ ( v1_zfmisc_1 @ X23 )
      | ( X23
        = ( k6_domain_1 @ X23 @ ( sk_B @ X23 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('3',plain,(
    ! [X23: $i] :
      ( ~ ( v1_zfmisc_1 @ X23 )
      | ( m1_subset_1 @ ( sk_B @ X23 ) @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['14','19'])).

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

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_tarski @ X20 )
       != ( k2_xboole_0 @ X18 @ X19 ) )
      | ( zip_tseitin_2 @ X19 @ X18 @ X20 )
      | ( zip_tseitin_1 @ X19 @ X18 @ X20 )
      | ( zip_tseitin_0 @ X19 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X15 ) )
      | ~ ( zip_tseitin_2 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_tarski @ X14 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','35'])).

thf('37',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uECGlv4LIW
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 62 iterations in 0.036s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(t1_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.50           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.50              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.22/0.50  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf(d1_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.50         ( ?[B:$i]:
% 0.22/0.50           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X23 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X23)
% 0.22/0.50          | ((X23) = (k6_domain_1 @ X23 @ (sk_B @ X23)))
% 0.22/0.50          | (v1_xboole_0 @ X23))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X23 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X23)
% 0.22/0.50          | (m1_subset_1 @ (sk_B @ X23) @ X23)
% 0.22/0.50          | (v1_xboole_0 @ X23))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X21)
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ X21)
% 0.22/0.50          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.50          | (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['2', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf('10', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(l32_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.50  thf('12', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf(t98_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X5 @ X6)
% 0.22/0.50           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t4_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X5 @ X6)
% 0.22/0.50           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf(t1_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('18', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.50  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '19'])).
% 0.22/0.50  thf(t43_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.50          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.50          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_4, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_6, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_7, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         (((k1_tarski @ X20) != (k2_xboole_0 @ X18 @ X19))
% 0.22/0.50          | (zip_tseitin_2 @ X19 @ X18 @ X20)
% 0.22/0.50          | (zip_tseitin_1 @ X19 @ X18 @ X20)
% 0.22/0.50          | (zip_tseitin_0 @ X19 @ X18 @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ X0) != (sk_B_1))
% 0.22/0.50          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) != (sk_B_1))
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.22/0.50          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.22/0.50          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (((zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.50      inference('simplify_reflect+', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         (((X17) = (k1_tarski @ X15)) | ~ (zip_tseitin_2 @ X17 @ X16 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.50        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (((X13) = (k1_tarski @ X14)) | ~ (zip_tseitin_1 @ X13 @ X12 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.22/0.50        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1)
% 0.22/0.50        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.50        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.22/0.50        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.50  thf('32', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.22/0.50        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.22/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (((X11) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X11 @ X10 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1))
% 0.22/0.50        | (v1_xboole_0 @ sk_B_1)
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['8', '35'])).
% 0.22/0.50  thf('37', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain, (((sk_A) != (sk_B_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('40', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('41', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.50      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['1', '42'])).
% 0.22/0.50  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
