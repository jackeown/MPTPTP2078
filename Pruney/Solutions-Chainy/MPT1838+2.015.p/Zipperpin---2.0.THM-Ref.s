%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UqxhtOfjVo

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 (  94 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  494 ( 753 expanded)
%              Number of equality atoms :   51 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( X24
        = ( k6_domain_1 @ X24 @ ( sk_B_1 @ X24 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
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
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_tarski @ X19 )
       != ( k2_xboole_0 @ X17 @ X18 ) )
      | ( zip_tseitin_2 @ X18 @ X17 @ X19 )
      | ( zip_tseitin_1 @ X18 @ X17 @ X19 )
      | ( zip_tseitin_0 @ X18 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_B_2 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_B_2 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( zip_tseitin_2 @ sk_B_2 @ sk_A @ ( sk_B_1 @ X0 ) )
      | ( zip_tseitin_1 @ sk_B_2 @ sk_A @ ( sk_B_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_B_2 @ sk_A @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_1 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( zip_tseitin_0 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_1 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_2 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ~ ( zip_tseitin_2 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( zip_tseitin_1 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( zip_tseitin_0 @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k1_tarski @ X8 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A = sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UqxhtOfjVo
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 44 iterations in 0.024s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.48  thf(t1_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.21/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d1_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.48         ( ?[B:$i]:
% 0.21/0.48           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X24 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X24)
% 0.21/0.48          | ((X24) = (k6_domain_1 @ X24 @ (sk_B_1 @ X24)))
% 0.21/0.48          | (v1_xboole_0 @ X24))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X24 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X24)
% 0.21/0.48          | (m1_subset_1 @ (sk_B_1 @ X24) @ X24)
% 0.21/0.48          | (v1_xboole_0 @ X24))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X22)
% 0.21/0.48          | ~ (m1_subset_1 @ X23 @ X22)
% 0.21/0.48          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t12_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.48  thf('11', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(t43_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.48          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_4, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_6, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_7, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         (((k1_tarski @ X19) != (k2_xboole_0 @ X17 @ X18))
% 0.21/0.48          | (zip_tseitin_2 @ X18 @ X17 @ X19)
% 0.21/0.48          | (zip_tseitin_1 @ X18 @ X17 @ X19)
% 0.21/0.48          | (zip_tseitin_0 @ X18 @ X17 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (sk_B_2))
% 0.21/0.48          | (zip_tseitin_0 @ sk_B_2 @ sk_A @ X0)
% 0.21/0.48          | (zip_tseitin_1 @ sk_B_2 @ sk_A @ X0)
% 0.21/0.48          | (zip_tseitin_2 @ sk_B_2 @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) != (sk_B_2))
% 0.21/0.48          | (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.48          | (zip_tseitin_2 @ sk_B_2 @ sk_A @ (sk_B_1 @ X0))
% 0.21/0.48          | (zip_tseitin_1 @ sk_B_2 @ sk_A @ (sk_B_1 @ X0))
% 0.21/0.48          | (zip_tseitin_0 @ sk_B_2 @ sk_A @ (sk_B_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((zip_tseitin_0 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (zip_tseitin_1 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (zip_tseitin_2 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((zip_tseitin_0 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (zip_tseitin_1 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (zip_tseitin_2 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.48      inference('simplify_reflect+', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         (((X15) = (k1_tarski @ X14)) | ~ (zip_tseitin_2 @ X16 @ X15 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | (zip_tseitin_1 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (zip_tseitin_0 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (((X11) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X12 @ X11 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.21/0.48        | (zip_tseitin_0 @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_B_2))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (((X9) = (k1_tarski @ X8)) | ~ (zip_tseitin_0 @ X10 @ X9 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.21/0.48        | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.48  thf('25', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B_1 @ sk_B_2))))),
% 0.21/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_A) = (sk_B_2))
% 0.21/0.48        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['7', '26'])).
% 0.21/0.48  thf('28', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_A) = (sk_B_2)) | (v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, (((sk_A) != (sk_B_2))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('34', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.48  thf('39', plain, ($false),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '33', '38'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
