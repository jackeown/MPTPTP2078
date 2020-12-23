%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OwI2HoTceb

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 111 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   23
%              Number of atoms          :  558 ( 884 expanded)
%              Number of equality atoms :   59 (  86 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,
    ( ( k1_xboole_0 != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( v1_zfmisc_1 @ X25 )
      | ( X25
        = ( k6_domain_1 @ X25 @ ( sk_B @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
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
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_tarski @ X22 )
       != ( k2_xboole_0 @ X20 @ X21 ) )
      | ( zip_tseitin_2 @ X21 @ X20 @ X22 )
      | ( zip_tseitin_1 @ X21 @ X20 @ X22 )
      | ( zip_tseitin_0 @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X19
        = ( k1_tarski @ X17 ) )
      | ~ ( zip_tseitin_2 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k1_tarski @ X16 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('28',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_A @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('33',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','33'])).

thf('35',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['41'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OwI2HoTceb
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:23:22 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 53 iterations in 0.029s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.23/0.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.23/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(t1_tex_2, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.51           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.51              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.23/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(l32_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i]:
% 0.23/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.51  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(t83_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X6 : $i, X8 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      ((((k1_xboole_0) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(d1_tex_2, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51       ( ( v1_zfmisc_1 @ A ) <=>
% 0.23/0.51         ( ?[B:$i]:
% 0.23/0.51           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X25 : $i]:
% 0.23/0.51         (~ (v1_zfmisc_1 @ X25)
% 0.23/0.51          | ((X25) = (k6_domain_1 @ X25 @ (sk_B @ X25)))
% 0.23/0.51          | (v1_xboole_0 @ X25))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X25 : $i]:
% 0.23/0.51         (~ (v1_zfmisc_1 @ X25)
% 0.23/0.51          | (m1_subset_1 @ (sk_B @ X25) @ X25)
% 0.23/0.51          | (v1_xboole_0 @ X25))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X23 : $i, X24 : $i]:
% 0.23/0.51         ((v1_xboole_0 @ X23)
% 0.23/0.51          | ~ (m1_subset_1 @ X24 @ X23)
% 0.23/0.51          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_xboole_0 @ X0)
% 0.23/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.51          | (v1_xboole_0 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | (v1_xboole_0 @ X0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.51          | (v1_xboole_0 @ X0)
% 0.23/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | (v1_xboole_0 @ X0)
% 0.23/0.51          | ~ (v1_zfmisc_1 @ X0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['6', '10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | (v1_xboole_0 @ X0)
% 0.23/0.51          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | (v1_xboole_0 @ X0)
% 0.23/0.51          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.51  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(t98_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i]:
% 0.23/0.51         ((k2_xboole_0 @ X9 @ X10)
% 0.23/0.51           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.51  thf(t5_boole, axiom,
% 0.23/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.51  thf('17', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.51  thf('18', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.51  thf(t43_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.51          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.51          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.51          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.23/0.51  thf(zf_stmt_2, axiom,
% 0.23/0.51    (![C:$i,B:$i,A:$i]:
% 0.23/0.51     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.23/0.51       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.23/0.51  thf(zf_stmt_4, axiom,
% 0.23/0.51    (![C:$i,B:$i,A:$i]:
% 0.23/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.23/0.51       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.23/0.51  thf(zf_stmt_6, axiom,
% 0.23/0.51    (![C:$i,B:$i,A:$i]:
% 0.23/0.51     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.23/0.51       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_7, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.51          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.23/0.51          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.23/0.51          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.51         (((k1_tarski @ X22) != (k2_xboole_0 @ X20 @ X21))
% 0.23/0.51          | (zip_tseitin_2 @ X21 @ X20 @ X22)
% 0.23/0.51          | (zip_tseitin_1 @ X21 @ X20 @ X22)
% 0.23/0.51          | (zip_tseitin_0 @ X21 @ X20 @ X22))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_tarski @ X0) != (sk_B_1))
% 0.23/0.51          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ X0)
% 0.23/0.51          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ X0)
% 0.23/0.51          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((X0) != (sk_B_1))
% 0.23/0.51          | (v1_xboole_0 @ X0)
% 0.23/0.51          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.51          | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.23/0.51          | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ X0))
% 0.23/0.51          | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (((zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.23/0.51        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.51  thf('23', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (zip_tseitin_2 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.51      inference('simplify_reflect+', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.51         (((X19) = (k1_tarski @ X17)) | ~ (zip_tseitin_2 @ X19 @ X18 @ X17))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((v1_xboole_0 @ sk_B_1)
% 0.23/0.51        | (zip_tseitin_1 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.51         (((X15) = (k1_tarski @ X16)) | ~ (zip_tseitin_1 @ X15 @ X14 @ X16))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.23/0.51        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | (v1_xboole_0 @ sk_B_1)
% 0.23/0.51        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      (((v1_xboole_0 @ sk_B_1)
% 0.23/0.51        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.23/0.51        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.23/0.51  thf('30', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.23/0.51        | (zip_tseitin_0 @ sk_A @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.23/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.51         (((X13) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X13 @ X12 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('34', plain,
% 0.23/0.51      ((((sk_A) = (sk_B_1))
% 0.23/0.51        | (v1_xboole_0 @ sk_B_1)
% 0.23/0.51        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.23/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['12', '33'])).
% 0.23/0.51  thf('35', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.51  thf('37', plain, (((sk_A) != (sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('38', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.23/0.51  thf('39', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.23/0.51  thf('41', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '40'])).
% 0.23/0.51  thf('42', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.23/0.51  thf(t69_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.51       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.23/0.51  thf('43', plain,
% 0.23/0.51      (![X4 : $i, X5 : $i]:
% 0.23/0.51         (~ (r1_xboole_0 @ X4 @ X5)
% 0.23/0.51          | ~ (r1_tarski @ X4 @ X5)
% 0.23/0.51          | (v1_xboole_0 @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.23/0.51  thf('44', plain, (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.51  thf('45', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('46', plain, ((v1_xboole_0 @ sk_A)),
% 0.23/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.23/0.51  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
