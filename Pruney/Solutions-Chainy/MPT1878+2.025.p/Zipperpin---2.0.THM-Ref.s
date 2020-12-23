%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iPXStJ9AB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 111 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  537 ( 838 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('1',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v2_tex_2 @ X22 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( X20 = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('42',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iPXStJ9AB
% 0.15/0.37  % Computer   : n018.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:14:42 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 78 iterations in 0.065s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.55  thf(t46_tex_2, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55            ( l1_pre_topc @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.22/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(l13_xboole_0, axiom,
% 0.22/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.55  thf('4', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.55  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.55  thf(d1_xboole_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.55  thf(t1_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i]:
% 0.22/0.55         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X18)
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ X18)
% 0.22/0.55          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X0)
% 0.22/0.55          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf(t36_tex_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.22/0.55          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23) @ X24)
% 0.22/0.55          | ~ (l1_pre_topc @ X24)
% 0.22/0.55          | ~ (v2_pre_topc @ X24)
% 0.22/0.55          | (v2_struct_0 @ X24))),
% 0.22/0.55      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | (v2_tex_2 @ 
% 0.22/0.55             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.22/0.55             X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['11', '14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf(dt_k6_domain_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X16)
% 0.22/0.55          | ~ (m1_subset_1 @ X17 @ X16)
% 0.22/0.55          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X0)
% 0.22/0.55          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.22/0.55             (k1_zfmisc_1 @ X0))
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.22/0.55          | (v1_xboole_0 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup+', [status(thm)], ['17', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X0)
% 0.22/0.55          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(d7_tex_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.55             ( ( v2_tex_2 @ B @ A ) & 
% 0.22/0.55               ( ![C:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.55                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.55          | ~ (v3_tex_2 @ X20 @ X21)
% 0.22/0.55          | ~ (v2_tex_2 @ X22 @ X21)
% 0.22/0.55          | ~ (r1_tarski @ X20 @ X22)
% 0.22/0.55          | ((X20) = (X22))
% 0.22/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.22/0.55          | ~ (l1_pre_topc @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ((k1_xboole_0) = (X1))
% 0.22/0.55          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.22/0.55          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.55          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.55  thf('27', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ((k1_xboole_0) = (X1))
% 0.22/0.55          | ~ (v2_tex_2 @ X1 @ X0)
% 0.22/0.55          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.55          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.55          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.22/0.55          | ~ (l1_pre_topc @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '28'])).
% 0.22/0.55  thf(t1_boole, axiom,
% 0.22/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.55  thf('30', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.55  thf(t49_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.55  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.55          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['16', '33'])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '35'])).
% 0.22/0.55  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.55  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('41', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.55  thf(fc2_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X15 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.22/0.55          | ~ (l1_struct_0 @ X15)
% 0.22/0.55          | (v2_struct_0 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.55  thf('43', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.55  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l1_pre_topc, axiom,
% 0.22/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.55  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['43', '46'])).
% 0.22/0.55  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
