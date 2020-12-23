%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PHe6DeJHNB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:20 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 143 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  545 (1136 expanded)
%              Number of equality atoms :   57 ( 118 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( X24
        = ( k6_domain_1 @ X24 @ ( sk_B @ X24 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('3',plain,(
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( m1_subset_1 @ ( sk_B @ X24 ) @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
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
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_tarski @ X21 )
       != ( k2_xboole_0 @ X19 @ X20 ) )
      | ( zip_tseitin_2 @ X20 @ X19 @ X21 )
      | ( zip_tseitin_1 @ X20 @ X19 @ X21 )
      | ( zip_tseitin_0 @ X20 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ X2 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X2 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ X1 @ X2 @ ( sk_B @ ( k2_xboole_0 @ X2 @ X1 ) ) )
      | ( zip_tseitin_1 @ X1 @ X2 @ ( sk_B @ ( k2_xboole_0 @ X2 @ X1 ) ) )
      | ( zip_tseitin_0 @ X1 @ X2 @ ( sk_B @ ( k2_xboole_0 @ X2 @ X1 ) ) )
      | ~ ( v1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) )
      | ( v1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k1_tarski @ X16 ) )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_tarski @ X15 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('30',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X10 ) ) ),
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
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PHe6DeJHNB
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 15:04:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 52 iterations in 0.030s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.34/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.34/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(t1_tex_2, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.34/0.52           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.34/0.52              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.34/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.34/0.52  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.34/0.52  thf(d1_tex_2, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52       ( ( v1_zfmisc_1 @ A ) <=>
% 0.34/0.52         ( ?[B:$i]:
% 0.34/0.52           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X24 : $i]:
% 0.34/0.52         (~ (v1_zfmisc_1 @ X24)
% 0.34/0.52          | ((X24) = (k6_domain_1 @ X24 @ (sk_B @ X24)))
% 0.34/0.52          | (v1_xboole_0 @ X24))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X24 : $i]:
% 0.34/0.52         (~ (v1_zfmisc_1 @ X24)
% 0.34/0.52          | (m1_subset_1 @ (sk_B @ X24) @ X24)
% 0.34/0.52          | (v1_xboole_0 @ X24))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.34/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.34/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i]:
% 0.34/0.52         ((v1_xboole_0 @ X22)
% 0.34/0.52          | ~ (m1_subset_1 @ X23 @ X22)
% 0.34/0.52          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((v1_xboole_0 @ X0)
% 0.34/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.34/0.52          | (v1_xboole_0 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.34/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | (v1_xboole_0 @ X0))),
% 0.34/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.34/0.52          | (v1_xboole_0 @ X0)
% 0.34/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | (v1_xboole_0 @ X0)
% 0.34/0.52          | ~ (v1_zfmisc_1 @ X0))),
% 0.34/0.52      inference('sup+', [status(thm)], ['2', '6'])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | (v1_xboole_0 @ X0)
% 0.34/0.52          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(l32_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.52  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf(t98_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X4 : $i, X5 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ X4 @ X5)
% 0.34/0.52           = (k5_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.34/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf(t5_boole, axiom,
% 0.34/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.52  thf('14', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.34/0.52  thf('15', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | (v1_xboole_0 @ X0)
% 0.34/0.52          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf(t43_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.34/0.52          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.52          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.34/0.52          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.34/0.52  thf(zf_stmt_2, axiom,
% 0.34/0.52    (![C:$i,B:$i,A:$i]:
% 0.34/0.52     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.34/0.52       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.34/0.52  thf(zf_stmt_4, axiom,
% 0.34/0.52    (![C:$i,B:$i,A:$i]:
% 0.34/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.34/0.52       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.34/0.52  thf(zf_stmt_6, axiom,
% 0.34/0.52    (![C:$i,B:$i,A:$i]:
% 0.34/0.52     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.34/0.52       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_7, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.34/0.52          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.34/0.52          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.34/0.52          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.52         (((k1_tarski @ X21) != (k2_xboole_0 @ X19 @ X20))
% 0.34/0.52          | (zip_tseitin_2 @ X20 @ X19 @ X21)
% 0.34/0.52          | (zip_tseitin_1 @ X20 @ X19 @ X21)
% 0.34/0.52          | (zip_tseitin_0 @ X20 @ X19 @ X21))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 0.34/0.52          | (v1_xboole_0 @ X0)
% 0.34/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.34/0.52          | (zip_tseitin_0 @ X1 @ X2 @ (sk_B @ X0))
% 0.34/0.52          | (zip_tseitin_1 @ X1 @ X2 @ (sk_B @ X0))
% 0.34/0.52          | (zip_tseitin_2 @ X1 @ X2 @ (sk_B @ X0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X1 : $i, X2 : $i]:
% 0.34/0.52         ((zip_tseitin_2 @ X1 @ X2 @ (sk_B @ (k2_xboole_0 @ X2 @ X1)))
% 0.34/0.52          | (zip_tseitin_1 @ X1 @ X2 @ (sk_B @ (k2_xboole_0 @ X2 @ X1)))
% 0.34/0.52          | (zip_tseitin_0 @ X1 @ X2 @ (sk_B @ (k2_xboole_0 @ X2 @ X1)))
% 0.34/0.52          | ~ (v1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1))
% 0.34/0.52          | (v1_xboole_0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.34/0.52        | (v1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.34/0.52        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ 
% 0.34/0.52           (sk_B @ (k2_xboole_0 @ sk_B_1 @ sk_A)))
% 0.34/0.52        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ 
% 0.34/0.52           (sk_B @ (k2_xboole_0 @ sk_B_1 @ sk_A)))
% 0.34/0.52        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ 
% 0.34/0.52           (sk_B @ (k2_xboole_0 @ sk_B_1 @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['15', '19'])).
% 0.34/0.52  thf('21', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('22', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('23', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('24', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('25', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (((v1_xboole_0 @ sk_B_1)
% 0.34/0.52        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.52         (((X18) = (k1_tarski @ X16)) | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (((zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | (v1_xboole_0 @ sk_B_1)
% 0.34/0.52        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (((X14) = (k1_tarski @ X15)) | ~ (zip_tseitin_1 @ X14 @ X13 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.34/0.52        | (v1_xboole_0 @ sk_B_1)
% 0.34/0.52        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (((zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.34/0.52        | (v1_xboole_0 @ sk_B_1)
% 0.34/0.52        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.34/0.52  thf('32', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.34/0.52        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.34/0.52      inference('clc', [status(thm)], ['31', '32'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.52         (((X12) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X12 @ X11 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))) | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      ((((sk_A) = (sk_B_1))
% 0.34/0.52        | (v1_xboole_0 @ sk_B_1)
% 0.34/0.52        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.34/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['8', '35'])).
% 0.34/0.52  thf('37', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.34/0.52  thf('39', plain, (((sk_A) != (sk_B_1))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('40', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.52      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.34/0.52  thf('41', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.34/0.52      inference('clc', [status(thm)], ['40', '41'])).
% 0.34/0.52  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.34/0.52      inference('demod', [status(thm)], ['1', '42'])).
% 0.34/0.52  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
