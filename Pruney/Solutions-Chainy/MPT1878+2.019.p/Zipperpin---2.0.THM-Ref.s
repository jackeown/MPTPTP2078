%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.irX24T4PLs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:05 EST 2020

% Result     : Theorem 2.48s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 128 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  544 ( 928 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X27 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X26 @ X25 )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( X24 = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.irX24T4PLs
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.48/2.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.48/2.67  % Solved by: fo/fo7.sh
% 2.48/2.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.48/2.67  % done 1692 iterations in 2.214s
% 2.48/2.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.48/2.67  % SZS output start Refutation
% 2.48/2.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.48/2.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.48/2.67  thf(sk_A_type, type, sk_A: $i).
% 2.48/2.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.48/2.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.48/2.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.48/2.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.48/2.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.48/2.67  thf(sk_B_type, type, sk_B: $i > $i).
% 2.48/2.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.48/2.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.48/2.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.48/2.67  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.48/2.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.48/2.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.48/2.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.48/2.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.48/2.67  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 2.48/2.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.48/2.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.48/2.67  thf(t46_tex_2, conjecture,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.48/2.67       ( ![B:$i]:
% 2.48/2.67         ( ( ( v1_xboole_0 @ B ) & 
% 2.48/2.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.48/2.67           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.48/2.67  thf(zf_stmt_0, negated_conjecture,
% 2.48/2.67    (~( ![A:$i]:
% 2.48/2.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.48/2.67            ( l1_pre_topc @ A ) ) =>
% 2.48/2.67          ( ![B:$i]:
% 2.48/2.67            ( ( ( v1_xboole_0 @ B ) & 
% 2.48/2.67                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.48/2.67              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 2.48/2.67    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 2.48/2.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf(d3_tarski, axiom,
% 2.48/2.67    (![A:$i,B:$i]:
% 2.48/2.67     ( ( r1_tarski @ A @ B ) <=>
% 2.48/2.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.48/2.67  thf('1', plain,
% 2.48/2.67      (![X4 : $i, X6 : $i]:
% 2.48/2.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.48/2.67      inference('cnf', [status(esa)], [d3_tarski])).
% 2.48/2.67  thf(d1_xboole_0, axiom,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.48/2.67  thf('2', plain,
% 2.48/2.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.48/2.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.48/2.67  thf('3', plain,
% 2.48/2.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['1', '2'])).
% 2.48/2.67  thf(t3_xboole_1, axiom,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.48/2.67  thf('4', plain,
% 2.48/2.67      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 2.48/2.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.48/2.67  thf('5', plain,
% 2.48/2.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.48/2.67      inference('sup-', [status(thm)], ['3', '4'])).
% 2.48/2.67  thf('6', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('7', plain, ((v1_xboole_0 @ sk_B_1)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('8', plain,
% 2.48/2.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.48/2.67      inference('sup-', [status(thm)], ['3', '4'])).
% 2.48/2.67  thf('9', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['7', '8'])).
% 2.48/2.67  thf('10', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 2.48/2.67      inference('demod', [status(thm)], ['6', '9'])).
% 2.48/2.67  thf('11', plain,
% 2.48/2.67      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 2.48/2.67      inference('sup+', [status(thm)], ['5', '10'])).
% 2.48/2.67  thf('12', plain,
% 2.48/2.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.48/2.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.48/2.67  thf(t1_subset, axiom,
% 2.48/2.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.48/2.67  thf('13', plain,
% 2.48/2.67      (![X15 : $i, X16 : $i]:
% 2.48/2.67         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 2.48/2.67      inference('cnf', [status(esa)], [t1_subset])).
% 2.48/2.67  thf('14', plain,
% 2.48/2.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['12', '13'])).
% 2.48/2.67  thf(redefinition_k6_domain_1, axiom,
% 2.48/2.67    (![A:$i,B:$i]:
% 2.48/2.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.48/2.67       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 2.48/2.67  thf('15', plain,
% 2.48/2.67      (![X22 : $i, X23 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ X22)
% 2.48/2.67          | ~ (m1_subset_1 @ X23 @ X22)
% 2.48/2.67          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 2.48/2.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.48/2.67  thf('16', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ X0)
% 2.48/2.67          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 2.48/2.67          | (v1_xboole_0 @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['14', '15'])).
% 2.48/2.67  thf('17', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 2.48/2.67          | (v1_xboole_0 @ X0))),
% 2.48/2.67      inference('simplify', [status(thm)], ['16'])).
% 2.48/2.67  thf('18', plain,
% 2.48/2.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['12', '13'])).
% 2.48/2.67  thf(t36_tex_2, axiom,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.48/2.67       ( ![B:$i]:
% 2.48/2.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.48/2.67           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 2.48/2.67  thf('19', plain,
% 2.48/2.67      (![X27 : $i, X28 : $i]:
% 2.48/2.67         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 2.48/2.67          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27) @ X28)
% 2.48/2.67          | ~ (l1_pre_topc @ X28)
% 2.48/2.67          | ~ (v2_pre_topc @ X28)
% 2.48/2.67          | (v2_struct_0 @ X28))),
% 2.48/2.67      inference('cnf', [status(esa)], [t36_tex_2])).
% 2.48/2.67  thf('20', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | (v2_struct_0 @ X0)
% 2.48/2.67          | ~ (v2_pre_topc @ X0)
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | (v2_tex_2 @ 
% 2.48/2.67             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 2.48/2.67             X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['18', '19'])).
% 2.48/2.67  thf('21', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | ~ (v2_pre_topc @ X0)
% 2.48/2.67          | (v2_struct_0 @ X0)
% 2.48/2.67          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.48/2.67      inference('sup+', [status(thm)], ['17', '20'])).
% 2.48/2.67  thf('22', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v2_struct_0 @ X0)
% 2.48/2.67          | ~ (v2_pre_topc @ X0)
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 2.48/2.67      inference('simplify', [status(thm)], ['21'])).
% 2.48/2.67  thf('23', plain,
% 2.48/2.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.48/2.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.48/2.67  thf(t63_subset_1, axiom,
% 2.48/2.67    (![A:$i,B:$i]:
% 2.48/2.67     ( ( r2_hidden @ A @ B ) =>
% 2.48/2.67       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.48/2.67  thf('24', plain,
% 2.48/2.67      (![X13 : $i, X14 : $i]:
% 2.48/2.67         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 2.48/2.67          | ~ (r2_hidden @ X13 @ X14))),
% 2.48/2.67      inference('cnf', [status(esa)], [t63_subset_1])).
% 2.48/2.67  thf('25', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ X0)
% 2.48/2.67          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 2.48/2.67      inference('sup-', [status(thm)], ['23', '24'])).
% 2.48/2.67  thf(t4_subset_1, axiom,
% 2.48/2.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.48/2.67  thf('26', plain,
% 2.48/2.67      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 2.48/2.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.48/2.67  thf(d7_tex_2, axiom,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( l1_pre_topc @ A ) =>
% 2.48/2.67       ( ![B:$i]:
% 2.48/2.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.48/2.67           ( ( v3_tex_2 @ B @ A ) <=>
% 2.48/2.67             ( ( v2_tex_2 @ B @ A ) & 
% 2.48/2.67               ( ![C:$i]:
% 2.48/2.67                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.48/2.67                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.48/2.67                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 2.48/2.67  thf('27', plain,
% 2.48/2.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.48/2.67         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 2.48/2.67          | ~ (v3_tex_2 @ X24 @ X25)
% 2.48/2.67          | ~ (v2_tex_2 @ X26 @ X25)
% 2.48/2.67          | ~ (r1_tarski @ X24 @ X26)
% 2.48/2.67          | ((X24) = (X26))
% 2.48/2.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 2.48/2.67          | ~ (l1_pre_topc @ X25))),
% 2.48/2.67      inference('cnf', [status(esa)], [d7_tex_2])).
% 2.48/2.67  thf('28', plain,
% 2.48/2.67      (![X0 : $i, X1 : $i]:
% 2.48/2.67         (~ (l1_pre_topc @ X0)
% 2.48/2.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.48/2.67          | ((k1_xboole_0) = (X1))
% 2.48/2.67          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 2.48/2.67          | ~ (v2_tex_2 @ X1 @ X0)
% 2.48/2.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['26', '27'])).
% 2.48/2.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.48/2.67  thf('29', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 2.48/2.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.48/2.67  thf('30', plain,
% 2.48/2.67      (![X0 : $i, X1 : $i]:
% 2.48/2.67         (~ (l1_pre_topc @ X0)
% 2.48/2.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.48/2.67          | ((k1_xboole_0) = (X1))
% 2.48/2.67          | ~ (v2_tex_2 @ X1 @ X0)
% 2.48/2.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 2.48/2.67      inference('demod', [status(thm)], ['28', '29'])).
% 2.48/2.67  thf('31', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.67          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.67          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 2.48/2.67          | ~ (l1_pre_topc @ X0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['25', '30'])).
% 2.48/2.67  thf(t1_boole, axiom,
% 2.48/2.67    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.48/2.67  thf('32', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.48/2.67      inference('cnf', [status(esa)], [t1_boole])).
% 2.48/2.67  thf(t49_zfmisc_1, axiom,
% 2.48/2.67    (![A:$i,B:$i]:
% 2.48/2.67     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 2.48/2.67  thf('33', plain,
% 2.48/2.67      (![X10 : $i, X11 : $i]:
% 2.48/2.67         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 2.48/2.67      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 2.48/2.67  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['32', '33'])).
% 2.48/2.67  thf('35', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.67          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 2.48/2.67          | ~ (l1_pre_topc @ X0))),
% 2.48/2.67      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 2.48/2.67  thf('36', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | ~ (v2_pre_topc @ X0)
% 2.48/2.67          | (v2_struct_0 @ X0)
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.67          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.48/2.67      inference('sup-', [status(thm)], ['22', '35'])).
% 2.48/2.67  thf('37', plain,
% 2.48/2.67      (![X0 : $i]:
% 2.48/2.67         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 2.48/2.67          | (v2_struct_0 @ X0)
% 2.48/2.67          | ~ (v2_pre_topc @ X0)
% 2.48/2.67          | ~ (l1_pre_topc @ X0)
% 2.48/2.67          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 2.48/2.67      inference('simplify', [status(thm)], ['36'])).
% 2.48/2.67  thf('38', plain,
% 2.48/2.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.48/2.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.48/2.67        | ~ (l1_pre_topc @ sk_A)
% 2.48/2.67        | ~ (v2_pre_topc @ sk_A)
% 2.48/2.67        | (v2_struct_0 @ sk_A))),
% 2.48/2.67      inference('sup-', [status(thm)], ['11', '37'])).
% 2.48/2.67  thf('39', plain, ((v1_xboole_0 @ sk_B_1)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('40', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.48/2.67      inference('sup-', [status(thm)], ['7', '8'])).
% 2.48/2.67  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.48/2.67      inference('demod', [status(thm)], ['39', '40'])).
% 2.48/2.67  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('44', plain,
% 2.48/2.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 2.48/2.67      inference('demod', [status(thm)], ['38', '41', '42', '43'])).
% 2.48/2.67  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 2.48/2.67      inference('clc', [status(thm)], ['44', '45'])).
% 2.48/2.67  thf(fc2_struct_0, axiom,
% 2.48/2.67    (![A:$i]:
% 2.48/2.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.48/2.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.48/2.67  thf('47', plain,
% 2.48/2.67      (![X21 : $i]:
% 2.48/2.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 2.48/2.67          | ~ (l1_struct_0 @ X21)
% 2.48/2.67          | (v2_struct_0 @ X21))),
% 2.48/2.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.48/2.67  thf('48', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 2.48/2.67      inference('sup-', [status(thm)], ['46', '47'])).
% 2.48/2.67  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 2.48/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.67  thf(dt_l1_pre_topc, axiom,
% 2.48/2.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.48/2.67  thf('50', plain,
% 2.48/2.67      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 2.48/2.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.48/2.67  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 2.48/2.67      inference('sup-', [status(thm)], ['49', '50'])).
% 2.48/2.67  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 2.48/2.67      inference('demod', [status(thm)], ['48', '51'])).
% 2.48/2.67  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 2.48/2.67  
% 2.48/2.67  % SZS output end Refutation
% 2.48/2.67  
% 2.48/2.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
