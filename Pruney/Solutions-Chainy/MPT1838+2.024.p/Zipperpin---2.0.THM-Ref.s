%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7r8zd0YV6t

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:18 EST 2020

% Result     : Theorem 13.36s
% Output     : Refutation 13.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 107 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  578 ( 840 expanded)
%              Number of equality atoms :   58 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ~ ( v1_zfmisc_1 @ X42 )
      | ( X42
        = ( k6_domain_1 @ X42 @ ( sk_B @ X42 ) ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X42: $i] :
      ( ~ ( v1_zfmisc_1 @ X42 )
      | ( m1_subset_1 @ ( sk_B @ X42 ) @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ X40 )
      | ( ( k6_domain_1 @ X40 @ X41 )
        = ( k1_tarski @ X41 ) ) ) ),
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
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_tarski @ X37 )
       != ( k2_xboole_0 @ X35 @ X36 ) )
      | ( zip_tseitin_2 @ X36 @ X35 @ X37 )
      | ( zip_tseitin_1 @ X36 @ X35 @ X37 )
      | ( zip_tseitin_0 @ X36 @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) )
      | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_2 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ~ ( zip_tseitin_2 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( zip_tseitin_0 @ sk_B_1 @ sk_A @ ( sk_B @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ~ ( zip_tseitin_0 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['31','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ X25 )
      | ( ( k4_xboole_0 @ X23 @ X25 )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X20 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7r8zd0YV6t
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 13.36/13.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.36/13.59  % Solved by: fo/fo7.sh
% 13.36/13.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.36/13.59  % done 21302 iterations in 13.137s
% 13.36/13.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.36/13.59  % SZS output start Refutation
% 13.36/13.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.36/13.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.36/13.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 13.36/13.59  thf(sk_B_type, type, sk_B: $i > $i).
% 13.36/13.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 13.36/13.59  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 13.36/13.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.36/13.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.36/13.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.36/13.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.36/13.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.36/13.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.36/13.59  thf(sk_A_type, type, sk_A: $i).
% 13.36/13.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 13.36/13.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.36/13.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.36/13.59  thf(t1_tex_2, conjecture,
% 13.36/13.59    (![A:$i]:
% 13.36/13.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 13.36/13.59       ( ![B:$i]:
% 13.36/13.59         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 13.36/13.59           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 13.36/13.59  thf(zf_stmt_0, negated_conjecture,
% 13.36/13.59    (~( ![A:$i]:
% 13.36/13.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 13.36/13.59          ( ![B:$i]:
% 13.36/13.59            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 13.36/13.59              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 13.36/13.59    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 13.36/13.59  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf(d1_tex_2, axiom,
% 13.36/13.59    (![A:$i]:
% 13.36/13.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 13.36/13.59       ( ( v1_zfmisc_1 @ A ) <=>
% 13.36/13.59         ( ?[B:$i]:
% 13.36/13.59           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 13.36/13.59  thf('1', plain,
% 13.36/13.59      (![X42 : $i]:
% 13.36/13.59         (~ (v1_zfmisc_1 @ X42)
% 13.36/13.59          | ((X42) = (k6_domain_1 @ X42 @ (sk_B @ X42)))
% 13.36/13.59          | (v1_xboole_0 @ X42))),
% 13.36/13.59      inference('cnf', [status(esa)], [d1_tex_2])).
% 13.36/13.59  thf('2', plain,
% 13.36/13.59      (![X42 : $i]:
% 13.36/13.59         (~ (v1_zfmisc_1 @ X42)
% 13.36/13.59          | (m1_subset_1 @ (sk_B @ X42) @ X42)
% 13.36/13.59          | (v1_xboole_0 @ X42))),
% 13.36/13.59      inference('cnf', [status(esa)], [d1_tex_2])).
% 13.36/13.59  thf(redefinition_k6_domain_1, axiom,
% 13.36/13.59    (![A:$i,B:$i]:
% 13.36/13.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 13.36/13.59       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 13.36/13.59  thf('3', plain,
% 13.36/13.59      (![X40 : $i, X41 : $i]:
% 13.36/13.59         ((v1_xboole_0 @ X40)
% 13.36/13.59          | ~ (m1_subset_1 @ X41 @ X40)
% 13.36/13.59          | ((k6_domain_1 @ X40 @ X41) = (k1_tarski @ X41)))),
% 13.36/13.59      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 13.36/13.59  thf('4', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         ((v1_xboole_0 @ X0)
% 13.36/13.59          | ~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 13.36/13.59          | (v1_xboole_0 @ X0))),
% 13.36/13.59      inference('sup-', [status(thm)], ['2', '3'])).
% 13.36/13.59  thf('5', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 13.36/13.59          | ~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | (v1_xboole_0 @ X0))),
% 13.36/13.59      inference('simplify', [status(thm)], ['4'])).
% 13.36/13.59  thf('6', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 13.36/13.59          | (v1_xboole_0 @ X0)
% 13.36/13.59          | ~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | (v1_xboole_0 @ X0)
% 13.36/13.59          | ~ (v1_zfmisc_1 @ X0))),
% 13.36/13.59      inference('sup+', [status(thm)], ['1', '5'])).
% 13.36/13.59  thf('7', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | (v1_xboole_0 @ X0)
% 13.36/13.59          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 13.36/13.59      inference('simplify', [status(thm)], ['6'])).
% 13.36/13.59  thf('8', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | (v1_xboole_0 @ X0)
% 13.36/13.59          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 13.36/13.59      inference('simplify', [status(thm)], ['6'])).
% 13.36/13.59  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf(t12_xboole_1, axiom,
% 13.36/13.59    (![A:$i,B:$i]:
% 13.36/13.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 13.36/13.59  thf('10', plain,
% 13.36/13.59      (![X10 : $i, X11 : $i]:
% 13.36/13.59         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 13.36/13.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 13.36/13.59  thf('11', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 13.36/13.59      inference('sup-', [status(thm)], ['9', '10'])).
% 13.36/13.59  thf(t43_zfmisc_1, axiom,
% 13.36/13.59    (![A:$i,B:$i,C:$i]:
% 13.36/13.59     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 13.36/13.59          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 13.36/13.59          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 13.36/13.59          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 13.36/13.59  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 13.36/13.59  thf(zf_stmt_2, axiom,
% 13.36/13.59    (![C:$i,B:$i,A:$i]:
% 13.36/13.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 13.36/13.59       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 13.36/13.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.36/13.59  thf(zf_stmt_4, axiom,
% 13.36/13.59    (![C:$i,B:$i,A:$i]:
% 13.36/13.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.36/13.59       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 13.36/13.59  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 13.36/13.59  thf(zf_stmt_6, axiom,
% 13.36/13.59    (![C:$i,B:$i,A:$i]:
% 13.36/13.59     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 13.36/13.59       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 13.36/13.59  thf(zf_stmt_7, axiom,
% 13.36/13.59    (![A:$i,B:$i,C:$i]:
% 13.36/13.59     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 13.36/13.59          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 13.36/13.59          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.36/13.59          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 13.36/13.59  thf('12', plain,
% 13.36/13.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 13.36/13.59         (((k1_tarski @ X37) != (k2_xboole_0 @ X35 @ X36))
% 13.36/13.59          | (zip_tseitin_2 @ X36 @ X35 @ X37)
% 13.36/13.59          | (zip_tseitin_1 @ X36 @ X35 @ X37)
% 13.36/13.59          | (zip_tseitin_0 @ X36 @ X35 @ X37))),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 13.36/13.59  thf('13', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (((k1_tarski @ X0) != (sk_B_1))
% 13.36/13.59          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ X0)
% 13.36/13.59          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ X0)
% 13.36/13.59          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ X0))),
% 13.36/13.59      inference('sup-', [status(thm)], ['11', '12'])).
% 13.36/13.59  thf('14', plain,
% 13.36/13.59      (![X0 : $i]:
% 13.36/13.59         (((X0) != (sk_B_1))
% 13.36/13.59          | (v1_xboole_0 @ X0)
% 13.36/13.59          | ~ (v1_zfmisc_1 @ X0)
% 13.36/13.59          | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 13.36/13.59          | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ X0))
% 13.36/13.59          | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ X0)))),
% 13.36/13.59      inference('sup-', [status(thm)], ['8', '13'])).
% 13.36/13.59  thf('15', plain,
% 13.36/13.59      (((zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1))),
% 13.36/13.59      inference('simplify', [status(thm)], ['14'])).
% 13.36/13.59  thf('16', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf('17', plain,
% 13.36/13.59      (((zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (zip_tseitin_2 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1))),
% 13.36/13.59      inference('simplify_reflect+', [status(thm)], ['15', '16'])).
% 13.36/13.59  thf('18', plain,
% 13.36/13.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 13.36/13.59         (((X33) = (k1_tarski @ X32)) | ~ (zip_tseitin_2 @ X34 @ X33 @ X32))),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.36/13.59  thf('19', plain,
% 13.36/13.59      (((v1_xboole_0 @ sk_B_1)
% 13.36/13.59        | (zip_tseitin_1 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 13.36/13.59      inference('sup-', [status(thm)], ['17', '18'])).
% 13.36/13.59  thf('20', plain,
% 13.36/13.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 13.36/13.59         (((X29) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X30 @ X29 @ X31))),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.36/13.59  thf('21', plain,
% 13.36/13.59      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 13.36/13.59        | (zip_tseitin_0 @ sk_B_1 @ sk_A @ (sk_B @ sk_B_1))
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1)
% 13.36/13.59        | ((sk_A) = (k1_xboole_0)))),
% 13.36/13.59      inference('sup-', [status(thm)], ['19', '20'])).
% 13.36/13.59  thf('22', plain,
% 13.36/13.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.36/13.59         (((X27) = (k1_tarski @ X26)) | ~ (zip_tseitin_0 @ X28 @ X27 @ X26))),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 13.36/13.59  thf('23', plain,
% 13.36/13.59      ((((sk_A) = (k1_xboole_0))
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1)
% 13.36/13.59        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 13.36/13.59        | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 13.36/13.59      inference('sup-', [status(thm)], ['21', '22'])).
% 13.36/13.59  thf('24', plain,
% 13.36/13.59      ((((sk_A) = (k1_tarski @ (sk_B @ sk_B_1)))
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1)
% 13.36/13.59        | ((sk_A) = (k1_xboole_0)))),
% 13.36/13.59      inference('simplify', [status(thm)], ['23'])).
% 13.36/13.59  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf('26', plain,
% 13.36/13.59      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 13.36/13.59      inference('clc', [status(thm)], ['24', '25'])).
% 13.36/13.59  thf('27', plain,
% 13.36/13.59      ((((sk_A) = (sk_B_1))
% 13.36/13.59        | (v1_xboole_0 @ sk_B_1)
% 13.36/13.59        | ~ (v1_zfmisc_1 @ sk_B_1)
% 13.36/13.59        | ((sk_A) = (k1_xboole_0)))),
% 13.36/13.59      inference('sup+', [status(thm)], ['7', '26'])).
% 13.36/13.59  thf('28', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf('29', plain,
% 13.36/13.59      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 13.36/13.59      inference('demod', [status(thm)], ['27', '28'])).
% 13.36/13.59  thf('30', plain, (((sk_A) != (sk_B_1))),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf('31', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 13.36/13.59      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 13.36/13.59  thf('32', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 13.36/13.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.36/13.59  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 13.36/13.59      inference('clc', [status(thm)], ['31', '32'])).
% 13.36/13.59  thf(t7_xboole_1, axiom,
% 13.36/13.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 13.36/13.59  thf('34', plain,
% 13.36/13.59      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 13.36/13.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 13.36/13.59  thf(t43_xboole_1, axiom,
% 13.36/13.59    (![A:$i,B:$i,C:$i]:
% 13.36/13.59     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 13.36/13.59       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 13.36/13.59  thf('35', plain,
% 13.36/13.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.36/13.59         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 13.36/13.59          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 13.36/13.59      inference('cnf', [status(esa)], [t43_xboole_1])).
% 13.36/13.59  thf('36', plain,
% 13.36/13.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 13.36/13.59      inference('sup-', [status(thm)], ['34', '35'])).
% 13.36/13.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 13.36/13.59  thf('37', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 13.36/13.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.36/13.59  thf(d10_xboole_0, axiom,
% 13.36/13.59    (![A:$i,B:$i]:
% 13.36/13.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.36/13.59  thf('38', plain,
% 13.36/13.59      (![X4 : $i, X6 : $i]:
% 13.36/13.59         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 13.36/13.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.36/13.59  thf('39', plain,
% 13.36/13.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 13.36/13.59      inference('sup-', [status(thm)], ['37', '38'])).
% 13.36/13.59  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.36/13.59      inference('sup-', [status(thm)], ['36', '39'])).
% 13.36/13.59  thf(t83_xboole_1, axiom,
% 13.36/13.59    (![A:$i,B:$i]:
% 13.36/13.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 13.36/13.59  thf('41', plain,
% 13.36/13.59      (![X23 : $i, X25 : $i]:
% 13.36/13.59         ((r1_xboole_0 @ X23 @ X25) | ((k4_xboole_0 @ X23 @ X25) != (X23)))),
% 13.36/13.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 13.36/13.59  thf('42', plain,
% 13.36/13.59      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 13.36/13.59      inference('sup-', [status(thm)], ['40', '41'])).
% 13.36/13.59  thf('43', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 13.36/13.59      inference('simplify', [status(thm)], ['42'])).
% 13.36/13.59  thf(t69_xboole_1, axiom,
% 13.36/13.59    (![A:$i,B:$i]:
% 13.36/13.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 13.36/13.59       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 13.36/13.59  thf('44', plain,
% 13.36/13.59      (![X19 : $i, X20 : $i]:
% 13.36/13.59         (~ (r1_xboole_0 @ X19 @ X20)
% 13.36/13.59          | ~ (r1_tarski @ X19 @ X20)
% 13.36/13.59          | (v1_xboole_0 @ X19))),
% 13.36/13.59      inference('cnf', [status(esa)], [t69_xboole_1])).
% 13.36/13.59  thf('45', plain,
% 13.36/13.59      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 13.36/13.59      inference('sup-', [status(thm)], ['43', '44'])).
% 13.36/13.59  thf('46', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 13.36/13.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.36/13.59  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.36/13.59      inference('demod', [status(thm)], ['45', '46'])).
% 13.36/13.59  thf('48', plain, ($false),
% 13.36/13.59      inference('demod', [status(thm)], ['0', '33', '47'])).
% 13.36/13.59  
% 13.36/13.59  % SZS output end Refutation
% 13.36/13.59  
% 13.44/13.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
