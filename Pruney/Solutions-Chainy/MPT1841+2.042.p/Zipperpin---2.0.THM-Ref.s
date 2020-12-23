%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MO2uFMFDry

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:34 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 286 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 (2327 expanded)
%              Number of equality atoms :   57 ( 141 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['3','4'])).

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
        = ( k6_domain_1 @ X28 @ ( sk_B_2 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('7',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( m1_subset_1 @ ( sk_B_2 @ X28 ) @ X28 )
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
      | ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_2 @ X0 ) )
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) )
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
        = ( k1_tarski @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_B_3
      = ( sk_B_2 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_3
      = ( sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_B_3
    = ( sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X28: $i] :
      ( ~ ( v1_zfmisc_1 @ X28 )
      | ( X28
        = ( k6_domain_1 @ X28 @ ( sk_B_2 @ X28 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('22',plain,
    ( ( sk_A
      = ( k6_domain_1 @ sk_A @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('25',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_3 )
      = ( k1_tarski @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_3 )
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X20 ) @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = X14 )
      | ( ( k1_tarski @ X15 )
       != ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
       != X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( ( sk_B_1 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ X17 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( ( ( sk_B_1 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X20: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_3 ) @ sk_A )
    | ( ( sk_B_1 @ ( k1_tarski @ sk_B_3 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('48',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('49',plain,
    ( ~ ( v1_subset_1 @ sk_A @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_3 )
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('52',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_3 ) @ sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_3 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('54',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X20 ) @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ X18 )
      | ( v1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( sk_B_1 @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MO2uFMFDry
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.58  % Solved by: fo/fo7.sh
% 0.35/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.58  % done 196 iterations in 0.122s
% 0.35/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.58  % SZS output start Refutation
% 0.35/0.58  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.35/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.58  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.35/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.35/0.58  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.35/0.58  thf(t6_tex_2, conjecture,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ A ) =>
% 0.35/0.58           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.35/0.58                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.58    (~( ![A:$i]:
% 0.35/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.58          ( ![B:$i]:
% 0.35/0.58            ( ( m1_subset_1 @ B @ A ) =>
% 0.35/0.58              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.35/0.58                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.35/0.58    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.35/0.58  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('1', plain, ((m1_subset_1 @ sk_B_3 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(t2_subset, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.58  thf('2', plain,
% 0.35/0.58      (![X21 : $i, X22 : $i]:
% 0.35/0.58         ((r2_hidden @ X21 @ X22)
% 0.35/0.58          | (v1_xboole_0 @ X22)
% 0.35/0.58          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.35/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.58  thf('3', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_3 @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.58  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('5', plain, ((r2_hidden @ sk_B_3 @ sk_A)),
% 0.35/0.58      inference('clc', [status(thm)], ['3', '4'])).
% 0.35/0.58  thf(d1_tex_2, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.58       ( ( v1_zfmisc_1 @ A ) <=>
% 0.35/0.58         ( ?[B:$i]:
% 0.35/0.58           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.35/0.58  thf('6', plain,
% 0.35/0.58      (![X28 : $i]:
% 0.35/0.58         (~ (v1_zfmisc_1 @ X28)
% 0.35/0.58          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_2 @ X28)))
% 0.35/0.58          | (v1_xboole_0 @ X28))),
% 0.35/0.58      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.35/0.58  thf('7', plain,
% 0.35/0.58      (![X28 : $i]:
% 0.35/0.58         (~ (v1_zfmisc_1 @ X28)
% 0.35/0.58          | (m1_subset_1 @ (sk_B_2 @ X28) @ X28)
% 0.35/0.58          | (v1_xboole_0 @ X28))),
% 0.35/0.58      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.35/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.58  thf('8', plain,
% 0.35/0.58      (![X26 : $i, X27 : $i]:
% 0.35/0.58         ((v1_xboole_0 @ X26)
% 0.35/0.58          | ~ (m1_subset_1 @ X27 @ X26)
% 0.35/0.58          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.35/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.58  thf('9', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         ((v1_xboole_0 @ X0)
% 0.35/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.58          | ((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.35/0.58          | (v1_xboole_0 @ X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.58  thf('10', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (((k6_domain_1 @ X0 @ (sk_B_2 @ X0)) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.35/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.58          | (v1_xboole_0 @ X0))),
% 0.35/0.58      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.58  thf('11', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (((X0) = (k1_tarski @ (sk_B_2 @ X0)))
% 0.35/0.58          | (v1_xboole_0 @ X0)
% 0.35/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.58          | (v1_xboole_0 @ X0)
% 0.35/0.58          | ~ (v1_zfmisc_1 @ X0))),
% 0.35/0.58      inference('sup+', [status(thm)], ['6', '10'])).
% 0.35/0.58  thf('12', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (v1_zfmisc_1 @ X0)
% 0.35/0.58          | (v1_xboole_0 @ X0)
% 0.35/0.58          | ((X0) = (k1_tarski @ (sk_B_2 @ X0))))),
% 0.35/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.58  thf(d1_tarski, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.58  thf('13', plain,
% 0.35/0.58      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X11 @ X10)
% 0.35/0.58          | ((X11) = (X8))
% 0.35/0.58          | ((X10) != (k1_tarski @ X8)))),
% 0.35/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.58  thf('14', plain,
% 0.35/0.58      (![X8 : $i, X11 : $i]:
% 0.35/0.58         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.35/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.58  thf('15', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X1 @ X0)
% 0.35/0.58          | (v1_xboole_0 @ X0)
% 0.35/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.58          | ((X1) = (sk_B_2 @ X0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['12', '14'])).
% 0.35/0.58  thf('16', plain,
% 0.35/0.58      ((((sk_B_3) = (sk_B_2 @ sk_A))
% 0.35/0.58        | ~ (v1_zfmisc_1 @ sk_A)
% 0.35/0.58        | (v1_xboole_0 @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['5', '15'])).
% 0.35/0.58  thf('17', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('18', plain, ((((sk_B_3) = (sk_B_2 @ sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.35/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.35/0.58  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('20', plain, (((sk_B_3) = (sk_B_2 @ sk_A))),
% 0.35/0.58      inference('clc', [status(thm)], ['18', '19'])).
% 0.35/0.58  thf('21', plain,
% 0.35/0.58      (![X28 : $i]:
% 0.35/0.58         (~ (v1_zfmisc_1 @ X28)
% 0.35/0.58          | ((X28) = (k6_domain_1 @ X28 @ (sk_B_2 @ X28)))
% 0.35/0.58          | (v1_xboole_0 @ X28))),
% 0.35/0.58      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.35/0.58  thf('22', plain,
% 0.35/0.58      ((((sk_A) = (k6_domain_1 @ sk_A @ sk_B_3))
% 0.35/0.58        | (v1_xboole_0 @ sk_A)
% 0.35/0.58        | ~ (v1_zfmisc_1 @ sk_A))),
% 0.35/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.35/0.58  thf('23', plain, ((m1_subset_1 @ sk_B_3 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('24', plain,
% 0.35/0.58      (![X26 : $i, X27 : $i]:
% 0.35/0.58         ((v1_xboole_0 @ X26)
% 0.35/0.58          | ~ (m1_subset_1 @ X27 @ X26)
% 0.35/0.58          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.35/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.58  thf('25', plain,
% 0.35/0.58      ((((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))
% 0.35/0.58        | (v1_xboole_0 @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.58  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('27', plain, (((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['25', '26'])).
% 0.35/0.58  thf('28', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('29', plain, ((((sk_A) = (k1_tarski @ sk_B_3)) | (v1_xboole_0 @ sk_A))),
% 0.35/0.58      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.35/0.58  thf('30', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('31', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.58  thf(rc3_subset_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ?[B:$i]:
% 0.35/0.58       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.35/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.35/0.58  thf('32', plain,
% 0.35/0.58      (![X20 : $i]: (m1_subset_1 @ (sk_B_1 @ X20) @ (k1_zfmisc_1 @ X20))),
% 0.35/0.58      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.58  thf(t3_subset, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.58  thf('33', plain,
% 0.35/0.58      (![X23 : $i, X24 : $i]:
% 0.35/0.58         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.58  thf('34', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.35/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.58  thf(t12_xboole_1, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.58  thf('35', plain,
% 0.35/0.58      (![X3 : $i, X4 : $i]:
% 0.35/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.35/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.58  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ (sk_B_1 @ X0) @ X0) = (X0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.58  thf(t44_zfmisc_1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.35/0.58          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.58          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.58  thf('37', plain,
% 0.35/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.58         (((X13) = (k1_xboole_0))
% 0.35/0.58          | ((X14) = (k1_xboole_0))
% 0.35/0.58          | ((X13) = (X14))
% 0.35/0.58          | ((k1_tarski @ X15) != (k2_xboole_0 @ X13 @ X14)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.35/0.58  thf('38', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (((k1_tarski @ X1) != (X0))
% 0.35/0.58          | ((sk_B_1 @ X0) = (X0))
% 0.35/0.58          | ((X0) = (k1_xboole_0))
% 0.35/0.58          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.58  thf('39', plain,
% 0.35/0.58      (![X1 : $i]:
% 0.35/0.58         (((sk_B_1 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.35/0.58          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.35/0.58          | ((sk_B_1 @ (k1_tarski @ X1)) = (k1_tarski @ X1)))),
% 0.35/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.35/0.58  thf(t1_boole, axiom,
% 0.35/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.58  thf('40', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.35/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.58  thf(t49_zfmisc_1, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.35/0.58  thf('41', plain,
% 0.35/0.58      (![X16 : $i, X17 : $i]:
% 0.35/0.58         ((k2_xboole_0 @ (k1_tarski @ X16) @ X17) != (k1_xboole_0))),
% 0.35/0.58      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.35/0.58  thf('42', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.58  thf('43', plain,
% 0.35/0.58      (![X1 : $i]:
% 0.35/0.58         (((sk_B_1 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.35/0.58          | ((sk_B_1 @ (k1_tarski @ X1)) = (k1_tarski @ X1)))),
% 0.35/0.58      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.35/0.58  thf('44', plain, (![X20 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X20) @ X20)),
% 0.35/0.58      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.58  thf('45', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (v1_subset_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.35/0.58          | ((sk_B_1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.58  thf('46', plain,
% 0.35/0.58      ((~ (v1_subset_1 @ (k1_tarski @ sk_B_3) @ sk_A)
% 0.35/0.58        | ((sk_B_1 @ (k1_tarski @ sk_B_3)) = (k1_xboole_0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['31', '45'])).
% 0.35/0.58  thf('47', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.58  thf('48', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.58  thf('49', plain,
% 0.35/0.58      ((~ (v1_subset_1 @ sk_A @ sk_A) | ((sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.58      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.35/0.58  thf('50', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_3) @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('51', plain, (((k6_domain_1 @ sk_A @ sk_B_3) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['25', '26'])).
% 0.35/0.58  thf('52', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_3) @ sk_A)),
% 0.35/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.35/0.58  thf('53', plain, (((sk_A) = (k1_tarski @ sk_B_3))),
% 0.35/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.58  thf('54', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.35/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.58  thf('55', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.35/0.58      inference('demod', [status(thm)], ['49', '54'])).
% 0.35/0.58  thf('56', plain,
% 0.35/0.58      (![X20 : $i]: (m1_subset_1 @ (sk_B_1 @ X20) @ (k1_zfmisc_1 @ X20))),
% 0.35/0.58      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.58  thf(cc2_subset_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.58       ( ![B:$i]:
% 0.35/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.58           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.35/0.58  thf('57', plain,
% 0.35/0.58      (![X18 : $i, X19 : $i]:
% 0.35/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.35/0.58          | ~ (v1_xboole_0 @ X18)
% 0.35/0.58          | (v1_subset_1 @ X18 @ X19)
% 0.35/0.58          | (v1_xboole_0 @ X19))),
% 0.35/0.58      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.35/0.58  thf('58', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         ((v1_xboole_0 @ X0)
% 0.35/0.58          | (v1_subset_1 @ (sk_B_1 @ X0) @ X0)
% 0.35/0.58          | ~ (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.58  thf('59', plain, (![X20 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X20) @ X20)),
% 0.35/0.58      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.58  thf('60', plain,
% 0.35/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ (sk_B_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.35/0.58      inference('clc', [status(thm)], ['58', '59'])).
% 0.35/0.58  thf('61', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['55', '60'])).
% 0.35/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.58  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.58  thf('63', plain, ((v1_xboole_0 @ sk_A)),
% 0.35/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.35/0.58  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.35/0.58  
% 0.35/0.58  % SZS output end Refutation
% 0.35/0.58  
% 0.35/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
