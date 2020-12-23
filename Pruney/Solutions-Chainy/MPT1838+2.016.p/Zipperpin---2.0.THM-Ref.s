%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HUqeKwcG2y

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 (  99 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  523 ( 782 expanded)
%              Number of equality atoms :   56 (  77 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( X25
        = ( k6_domain_1 @ X25 @ ( sk_B @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('10',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( m1_subset_1 @ ( sk_B @ X25 ) @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_tarski @ X22 )
       != ( k2_xboole_0 @ X20 @ X21 ) )
      | ( zip_tseitin_2 @ X21 @ X20 @ X22 )
      | ( zip_tseitin_1 @ X21 @ X20 @ X22 )
      | ( zip_tseitin_0 @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18
        = ( k1_tarski @ X17 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','34'])).

thf('36',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['8','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HUqeKwcG2y
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 45 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(t1_tex_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.47           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.20/0.47              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.20/0.47  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('1', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf(t3_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('2', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.47  thf(t83_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X8 : $i, X10 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.47  thf(t69_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.47       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ X6 @ X7)
% 0.20/0.47          | ~ (r1_tarski @ X6 @ X7)
% 0.20/0.47          | (v1_xboole_0 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.47  thf(d1_tex_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.47         ( ?[B:$i]:
% 0.20/0.47           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X25 : $i]:
% 0.20/0.47         (~ (v1_zfmisc_1 @ X25)
% 0.20/0.47          | ((X25) = (k6_domain_1 @ X25 @ (sk_B @ X25)))
% 0.20/0.47          | (v1_xboole_0 @ X25))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X25 : $i]:
% 0.20/0.47         (~ (v1_zfmisc_1 @ X25)
% 0.20/0.47          | (m1_subset_1 @ (sk_B @ X25) @ X25)
% 0.20/0.47          | (v1_xboole_0 @ X25))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X23 : $i, X24 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X23)
% 0.20/0.47          | ~ (m1_subset_1 @ X24 @ X23)
% 0.20/0.47          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.47          | (v1_xboole_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | (v1_xboole_0 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.47          | (v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | (v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | (v1_xboole_0 @ X0)
% 0.20/0.47          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | (v1_xboole_0 @ X0)
% 0.20/0.47          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('17', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t12_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.47  thf('19', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf(t43_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.47          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.47          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.47          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_2, axiom,
% 0.20/0.47    (![C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.47       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_4, axiom,
% 0.20/0.47    (![C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.47       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_6, axiom,
% 0.20/0.47    (![C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.47       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_7, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.47          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.47          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.47          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.47         (((k1_tarski @ X22) != (k2_xboole_0 @ X20 @ X21))
% 0.20/0.47          | (zip_tseitin_2 @ X21 @ X20 @ X22)
% 0.20/0.47          | (zip_tseitin_1 @ X21 @ X20 @ X22)
% 0.20/0.47          | (zip_tseitin_0 @ X21 @ X20 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_tarski @ X0) != (sk_B_1))
% 0.20/0.47          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ X0)
% 0.20/0.47          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ X0)
% 0.20/0.47          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((X0) != (sk_B_1))
% 0.20/0.47          | (v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.47          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.47          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 0.20/0.47          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('simplify_reflect+', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         (((X18) = (k1_tarski @ X17)) | ~ (zip_tseitin_2 @ X19 @ X18 @ X17))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (((X14) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X15 @ X14 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.47        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((X12) = (k1_tarski @ X11)) | ~ (zip_tseitin_0 @ X13 @ X12 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((((sk_A) = (k1_xboole_0))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.47        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.47  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.20/0.47      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((sk_A) = (sk_B_1))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['15', '34'])).
% 0.20/0.47  thf('36', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '41'])).
% 0.20/0.47  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
