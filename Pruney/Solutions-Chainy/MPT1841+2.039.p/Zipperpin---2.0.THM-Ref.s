%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yBhamh4Cqh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:34 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 126 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  466 ( 839 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X19 ) @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_zfmisc_1 @ X30 )
      | ( X31 = X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( v1_xboole_0 @ X17 )
      | ( v1_subset_1 @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_subset_1 @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( sk_B_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1 @ sk_A )
    = sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X19: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('23',plain,(
    ~ ( v1_subset_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ X28 )
      | ( ( k6_domain_1 @ X28 @ X29 )
        = ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_zfmisc_1 @ X30 )
      | ( X31 = X30 )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['30','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['23','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yBhamh4Cqh
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 202 iterations in 0.134s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.61  thf(rc3_subset_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ?[B:$i]:
% 0.37/0.61       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.37/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (![X19 : $i]: (m1_subset_1 @ (sk_B_1 @ X19) @ (k1_zfmisc_1 @ X19))),
% 0.37/0.61      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i]:
% 0.37/0.61         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('2', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.61  thf(t1_tex_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.37/0.61           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X30 : $i, X31 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X30)
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X30)
% 0.37/0.61          | ((X31) = (X30))
% 0.37/0.61          | ~ (r1_tarski @ X31 @ X30)
% 0.37/0.61          | (v1_xboole_0 @ X31))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.37/0.61          | ((sk_B_1 @ X0) = (X0))
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.61  thf(d3_tarski, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X4 : $i, X6 : $i]:
% 0.37/0.61         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.61  thf(d1_xboole_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X20 : $i, X22 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf(cc2_subset_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.37/0.61          | ~ (v1_xboole_0 @ X17)
% 0.37/0.61          | (v1_subset_1 @ X17 @ X18)
% 0.37/0.61          | (v1_xboole_0 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ X1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | (v1_subset_1 @ X1 @ X0)
% 0.37/0.61          | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((v1_subset_1 @ X1 @ X0) | (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.61  thf(t6_tex_2, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.61           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.37/0.61                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.61              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.37/0.61                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.37/0.61  thf('13', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_subset_1 @ X0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain, (![X19 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X19) @ X19)),
% 0.37/0.61      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.61  thf('16', plain, (~ (v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_A)
% 0.37/0.61        | ~ (v1_zfmisc_1 @ sk_A)
% 0.37/0.61        | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '16'])).
% 0.37/0.61  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('19', plain, (((v1_xboole_0 @ sk_A) | ((sk_B_1 @ sk_A) = (sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('21', plain, (((sk_B_1 @ sk_A) = (sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['19', '20'])).
% 0.37/0.61  thf('22', plain, (![X19 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X19) @ X19)),
% 0.37/0.61      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.37/0.61  thf('23', plain, (~ (v1_subset_1 @ sk_A @ sk_A)),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('24', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('25', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.61       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X28)
% 0.37/0.61          | ~ (m1_subset_1 @ X29 @ X28)
% 0.37/0.61          | ((k6_domain_1 @ X28 @ X29) = (k1_tarski @ X29)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('29', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.37/0.61      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.37/0.61      inference('demod', [status(thm)], ['24', '29'])).
% 0.37/0.61  thf('31', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k6_domain_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.61       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X26)
% 0.37/0.61          | ~ (m1_subset_1 @ X27 @ X26)
% 0.37/0.61          | (m1_subset_1 @ (k6_domain_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26)))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('34', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.37/0.61      inference('clc', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.61  thf('36', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i]:
% 0.37/0.61         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('39', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X30 : $i, X31 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X30)
% 0.37/0.61          | ~ (v1_zfmisc_1 @ X30)
% 0.37/0.61          | ((X31) = (X30))
% 0.37/0.61          | ~ (r1_tarski @ X31 @ X30)
% 0.37/0.61          | (v1_xboole_0 @ X31))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.37/0.61        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.37/0.61        | ~ (v1_zfmisc_1 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.61  thf('42', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.37/0.61        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.61  thf('44', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      ((((k1_tarski @ sk_B_2) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.37/0.61      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t4_subset_1, axiom,
% 0.37/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i]:
% 0.37/0.61         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X7 : $i, X9 : $i]:
% 0.37/0.61         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['46', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      ((((k1_tarski @ sk_B_2) = (sk_A))
% 0.37/0.61        | ((k1_tarski @ sk_B_2) = (k1_xboole_0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['45', '52'])).
% 0.37/0.61  thf(t1_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.61  thf('54', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.61  thf(t49_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ (k1_tarski @ X14) @ X15) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.37/0.61  thf('56', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.37/0.61  thf('58', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.37/0.61      inference('demod', [status(thm)], ['30', '57'])).
% 0.37/0.61  thf('59', plain, ($false), inference('demod', [status(thm)], ['23', '58'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
