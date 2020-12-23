%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Abb8iwMyZ1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 458 expanded)
%              Number of leaves         :   25 ( 142 expanded)
%              Depth                    :   20
%              Number of atoms          :  498 (3414 expanded)
%              Number of equality atoms :   34 ( 150 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_B_1 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( sk_B_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_B_2 ) ) @ sk_A ),
    inference(demod,[status(thm)],['12','17'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ ( k1_tarski @ sk_B_2 ) ) )
    | ( ( sk_B_1 @ ( k1_tarski @ sk_B_2 ) )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ ( k1_tarski @ sk_B_2 ) ) )
    | ( ( sk_B_1 @ ( k1_tarski @ sk_B_2 ) )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_2 )
      = sk_A ) ),
    inference(clc,[status(thm)],['29','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_B_1 @ sk_A )
      = sk_A )
    | ( k1_xboole_0
      = ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('50',plain,
    ( ~ ( v1_subset_1 @ sk_A @ sk_A )
    | ( k1_xboole_0
      = ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('53',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_B_2 )
    = sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('58',plain,(
    ~ ( v1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( k1_xboole_0
    = ( sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('60',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('61',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_xboole_0 @ X11 )
      | ( v1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_subset_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['58','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Abb8iwMyZ1
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 133 iterations in 0.088s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.54  thf(t6_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.54           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.54                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.54              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.54                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.54  thf('0', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ X20)
% 0.21/0.54          | (m1_subset_1 @ (k6_domain_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('6', plain, ((r1_tarski @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf(rc3_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ?[B:$i]:
% 0.21/0.54       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('9', plain, (![X0 : $i]: (r1_tarski @ (sk_B_1 @ X0) @ X0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(t1_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.54       ( r1_tarski @ A @ C ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.54          | ~ (r1_tarski @ X5 @ X6)
% 0.21/0.54          | (r1_tarski @ X4 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ (sk_B_1 @ X0) @ X1) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((r1_tarski @ (sk_B_1 @ (k6_domain_1 @ sk_A @ sk_B_2)) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.54  thf('13', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X22)
% 0.21/0.54          | ~ (m1_subset_1 @ X23 @ X22)
% 0.21/0.54          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.21/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain, ((r1_tarski @ (sk_B_1 @ (k1_tarski @ sk_B_2)) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.54  thf(t1_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.54           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X24)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X24)
% 0.21/0.54          | ((X25) = (X24))
% 0.21/0.54          | ~ (r1_tarski @ X25 @ X24)
% 0.21/0.54          | (v1_xboole_0 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((v1_xboole_0 @ (sk_B_1 @ (k1_tarski @ sk_B_2)))
% 0.21/0.54        | ((sk_B_1 @ (k1_tarski @ sk_B_2)) = (sk_A))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((v1_xboole_0 @ (sk_B_1 @ (k1_tarski @ sk_B_2)))
% 0.21/0.54        | ((sk_B_1 @ (k1_tarski @ sk_B_2)) = (sk_A))
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain, ((r1_tarski @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('24', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.21/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X24)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X24)
% 0.21/0.54          | ((X25) = (X24))
% 0.21/0.54          | ~ (r1_tarski @ X25 @ X24)
% 0.21/0.54          | (v1_xboole_0 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.21/0.54        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tarski @ sk_B_2))
% 0.21/0.54        | ((k1_tarski @ sk_B_2) = (sk_A))
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf(t8_boole, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.54  thf(t1_boole, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.54  thf('31', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.54  thf(t49_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.54  thf('33', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((X0) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_xboole_0 @ (k1_tarski @ X1))
% 0.21/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X1 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.54  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('37', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.21/0.54      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B_2) = (sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['29', '37'])).
% 0.21/0.54  thf('39', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.21/0.54        | ((sk_B_1 @ sk_A) = (sk_A))
% 0.21/0.54        | (v1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['22', '40', '41'])).
% 0.21/0.54  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((((sk_B_1 @ sk_A) = (sk_A)) | (v1_xboole_0 @ (sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((((sk_B_1 @ sk_A) = (sk_A)) | ((k1_xboole_0) = (sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.54  thf('49', plain, (![X13 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ sk_A @ sk_A) | ((k1_xboole_0) = (sk_B_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.21/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('53', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain, (((k1_tarski @ sk_B_2) = (sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('55', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, (((k1_xboole_0) = (sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '55'])).
% 0.21/0.54  thf('57', plain, (![X13 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('58', plain, (~ (v1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain, (((k1_xboole_0) = (sk_B_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '55'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.21/0.54  thf('61', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf(cc2_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.54          | ~ (v1_xboole_0 @ X11)
% 0.21/0.54          | (v1_subset_1 @ X11 @ X12)
% 0.21/0.54          | (v1_xboole_0 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (((v1_xboole_0 @ sk_A)
% 0.21/0.54        | (v1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((v1_xboole_0 @ sk_A) | (v1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain, ((v1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain, ($false), inference('demod', [status(thm)], ['58', '67'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
