%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXi7zLWnGe

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 102 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  535 ( 794 expanded)
%              Number of equality atoms :   54 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_1 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('7',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_1 @ X28 ) @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,
    ( sk_B_2
    = ( k2_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_tarski @ X23 )
       != ( k2_xboole_0 @ X21 @ X22 ) )
      | ( zip_tseitin_2 @ X22 @ X21 @ X23 )
      | ( zip_tseitin_1 @ X22 @ X21 @ X23 )
      | ( zip_tseitin_0 @ X22 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ X0 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_2 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_2 @ ( sk_B_1 @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ sk_B_2 @ ( sk_B_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X20
        = ( k1_tarski @ X18 ) )
      | ~ ( zip_tseitin_2 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_tarski @ X17 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('35',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','35'])).

thf('37',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['5','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXi7zLWnGe
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 62 iterations in 0.039s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.49  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.22/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.22/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.49  thf(t1_tex_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.49              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.22/0.49  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.49  thf('1', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf(t7_ordinal1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X24 : $i, X25 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(d1_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.49         ( ?[B:$i]:
% 0.22/0.49           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X28 : $i]:
% 0.22/0.49         (~ (v1_zfmisc_1 @ X28)
% 0.22/0.49          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_1 @ X28)))
% 0.22/0.49          | (v1_xboole_0 @ X28))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X28 : $i]:
% 0.22/0.49         (~ (v1_zfmisc_1 @ X28)
% 0.22/0.49          | (m1_subset_1 @ (sk_B_1 @ X28) @ X28)
% 0.22/0.49          | (v1_xboole_0 @ X28))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X26 : $i, X27 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X26)
% 0.22/0.49          | ~ (m1_subset_1 @ X27 @ X26)
% 0.22/0.49          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0)
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.49          | (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['6', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.49  thf('14', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf(t39_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.22/0.49           = (k2_xboole_0 @ X8 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((k2_xboole_0 @ sk_B_2 @ k1_xboole_0) = (k2_xboole_0 @ sk_B_2 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf(t1_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('19', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.49  thf('20', plain, (((sk_B_2) = (k2_xboole_0 @ sk_B_2 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf(t43_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.49          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.49          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.49          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_2, axiom,
% 0.22/0.49    (![C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.22/0.49       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_4, axiom,
% 0.22/0.49    (![C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.49       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_6, axiom,
% 0.22/0.49    (![C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.22/0.49       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_7, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.49          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.22/0.49          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.49          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.49         (((k1_tarski @ X23) != (k2_xboole_0 @ X21 @ X22))
% 0.22/0.49          | (zip_tseitin_2 @ X22 @ X21 @ X23)
% 0.22/0.49          | (zip_tseitin_1 @ X22 @ X21 @ X23)
% 0.22/0.49          | (zip_tseitin_0 @ X22 @ X21 @ X23))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_tarski @ X0) != (sk_B_2))
% 0.22/0.49          | (zip_tseitin_0 @ sk_A @ sk_B_2 @ X0)
% 0.22/0.49          | (zip_tseitin_1 @ sk_A @ sk_B_2 @ X0)
% 0.22/0.49          | (zip_tseitin_2 @ sk_A @ sk_B_2 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((X0) != (sk_B_2))
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.49          | (zip_tseitin_2 @ sk_A @ sk_B_2 @ (sk_B_1 @ X0))
% 0.22/0.49          | (zip_tseitin_1 @ sk_A @ sk_B_2 @ (sk_B_1 @ X0))
% 0.22/0.49          | (zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (zip_tseitin_2 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.22/0.49        | (v1_xboole_0 @ sk_B_2))),
% 0.22/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.49  thf('25', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (zip_tseitin_2 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (v1_xboole_0 @ sk_B_2))),
% 0.22/0.49      inference('simplify_reflect+', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X20) = (k1_tarski @ X18)) | ~ (zip_tseitin_2 @ X20 @ X19 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_B_2)
% 0.22/0.49        | (zip_tseitin_1 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.49         (((X16) = (k1_tarski @ X17)) | ~ (zip_tseitin_1 @ X16 @ X15 @ X17))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.22/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | (v1_xboole_0 @ sk_B_2)
% 0.22/0.49        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_B_2)
% 0.22/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.22/0.49        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.49  thf('32', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.22/0.49        | (zip_tseitin_0 @ sk_A @ sk_B_2 @ (sk_B_1 @ sk_B_2)))),
% 0.22/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.49         (((X14) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X14 @ X13 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((((sk_A) = (sk_B_2))
% 0.22/0.49        | (v1_xboole_0 @ sk_B_2)
% 0.22/0.49        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['12', '35'])).
% 0.22/0.49  thf('37', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain, (((sk_A) != (sk_B_2))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.22/0.49  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '42'])).
% 0.22/0.49  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
