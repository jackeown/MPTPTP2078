%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ugy93FVbbd

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:34 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 127 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  481 ( 841 expanded)
%              Number of equality atoms :   30 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_zfmisc_1 @ X29 )
      | ( X30 = X29 )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','35'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X18 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_zfmisc_1 @ X29 )
      | ( X30 = X29 )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X18 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_xboole_0 @ X16 )
      | ( v1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( sk_B_1 @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X18: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('51',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 ) ) ),
    inference(clc,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X18: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','56'])).

thf('58',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ugy93FVbbd
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 242 iterations in 0.128s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.57  thf(t6_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ A ) =>
% 0.39/0.57           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.39/0.57                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( m1_subset_1 @ B @ A ) =>
% 0.39/0.57              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.39/0.57                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.39/0.57  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X27 : $i, X28 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X27)
% 0.39/0.57          | ~ (m1_subset_1 @ X28 @ X27)
% 0.39/0.57          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.39/0.57      inference('clc', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '5'])).
% 0.39/0.57  thf('7', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k6_domain_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X25)
% 0.39/0.57          | ~ (m1_subset_1 @ X26 @ X25)
% 0.39/0.57          | (m1_subset_1 @ (k6_domain_1 @ X25 @ X26) @ (k1_zfmisc_1 @ X25)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.39/0.57      inference('clc', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(t3_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf(t1_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.39/0.57           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X29)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X29)
% 0.39/0.57          | ((X30) = (X29))
% 0.39/0.57          | ~ (r1_tarski @ X30 @ X29)
% 0.39/0.57          | (v1_xboole_0 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.39/0.57        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.39/0.57        | ~ (v1_zfmisc_1 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.39/0.57        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((((k1_tarski @ sk_B_2) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B_2)))),
% 0.39/0.57      inference('clc', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X4 : $i, X6 : $i]:
% 0.39/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf(d1_xboole_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf(t4_subset_1, axiom,
% 0.39/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X7 : $i, X9 : $i]:
% 0.39/0.57         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((((k1_tarski @ sk_B_2) = (sk_A))
% 0.39/0.57        | ((k1_tarski @ sk_B_2) = (k1_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '30'])).
% 0.39/0.57  thf(t1_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('32', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.57  thf(t49_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i]:
% 0.39/0.57         ((k2_xboole_0 @ (k1_tarski @ X13) @ X14) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.57  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.57  thf('35', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.39/0.57  thf('36', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '35'])).
% 0.39/0.57  thf(rc3_subset_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ?[B:$i]:
% 0.39/0.57       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.39/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X18 : $i]: (m1_subset_1 @ (sk_B_1 @ X18) @ (k1_zfmisc_1 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('39', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X29)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X29)
% 0.39/0.57          | ((X30) = (X29))
% 0.39/0.57          | ~ (r1_tarski @ X30 @ X29)
% 0.39/0.57          | (v1_xboole_0 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.39/0.57          | ((sk_B_1 @ X0) = (X0))
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X18 : $i]: (m1_subset_1 @ (sk_B_1 @ X18) @ (k1_zfmisc_1 @ X18))),
% 0.39/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.57  thf(cc2_subset_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.39/0.57          | ~ (v1_xboole_0 @ X16)
% 0.39/0.57          | (v1_subset_1 @ X16 @ X17)
% 0.39/0.57          | (v1_xboole_0 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0)
% 0.39/0.57          | (v1_subset_1 @ (sk_B_1 @ X0) @ X0)
% 0.39/0.57          | ~ (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain, (![X18 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X18) @ X18)),
% 0.39/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ (sk_B_1 @ X0)) | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('clc', [status(thm)], ['44', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.57          | ((sk_B_1 @ X0) = (X0))
% 0.39/0.57          | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['41', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_B_1 @ X0) = (X0)) | ~ (v1_zfmisc_1 @ X0) | (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.57  thf('49', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (![X7 : $i, X9 : $i]:
% 0.39/0.57         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (![X0 : $i]: (((sk_B_1 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['49', '52'])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v1_zfmisc_1 @ X0) | ((sk_B_1 @ X0) = (X0)))),
% 0.39/0.57      inference('clc', [status(thm)], ['48', '53'])).
% 0.39/0.57  thf('55', plain, (![X18 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X18) @ X18)),
% 0.39/0.57      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      (![X0 : $i]: (~ (v1_subset_1 @ X0 @ X0) | ~ (v1_zfmisc_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.57  thf('57', plain, (~ (v1_zfmisc_1 @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['36', '56'])).
% 0.39/0.57  thf('58', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('59', plain, ($false), inference('demod', [status(thm)], ['57', '58'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
