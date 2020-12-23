%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ylljQqJ4s2

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 114 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  559 ( 923 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

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
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_3 ),
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
    sk_B_3 = k1_xboole_0 ),
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X27 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( X25 = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ylljQqJ4s2
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 498 iterations in 0.357s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.61/0.81  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.81  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.61/0.81  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.61/0.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.61/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.81  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.61/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.81  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.61/0.81  thf(t46_tex_2, conjecture,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( ( v1_xboole_0 @ B ) & 
% 0.61/0.81             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.81           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i]:
% 0.61/0.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.61/0.81            ( l1_pre_topc @ A ) ) =>
% 0.61/0.81          ( ![B:$i]:
% 0.61/0.81            ( ( ( v1_xboole_0 @ B ) & 
% 0.61/0.81                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.81              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.61/0.81  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('1', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('2', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(l13_xboole_0, axiom,
% 0.61/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.81  thf('4', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.81  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.61/0.81      inference('demod', [status(thm)], ['1', '4'])).
% 0.61/0.81  thf(d1_xboole_0, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.81  thf(t1_subset, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (![X17 : $i, X18 : $i]:
% 0.61/0.81         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.61/0.81      inference('cnf', [status(esa)], [t1_subset])).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.81  thf(redefinition_k6_domain_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.61/0.81       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X23 : $i, X24 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ X23)
% 0.61/0.81          | ~ (m1_subset_1 @ X24 @ X23)
% 0.61/0.81          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.61/0.81      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ X0)
% 0.61/0.81          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.61/0.81          | (v1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.61/0.81          | (v1_xboole_0 @ X0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['10'])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.81  thf(t36_tex_2, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.61/0.81           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (![X28 : $i, X29 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.61/0.81          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.61/0.81          | ~ (l1_pre_topc @ X29)
% 0.61/0.81          | ~ (v2_pre_topc @ X29)
% 0.61/0.81          | (v2_struct_0 @ X29))),
% 0.61/0.81      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | (v2_struct_0 @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | (v2_tex_2 @ 
% 0.61/0.81             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.61/0.81             X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.61/0.81          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | (v2_struct_0 @ X0)
% 0.61/0.81          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['11', '14'])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v2_struct_0 @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['15'])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.81  thf(t63_subset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.81       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((m1_subset_1 @ (k1_tarski @ X13) @ (k1_zfmisc_1 @ X14))
% 0.61/0.81          | ~ (r2_hidden @ X13 @ X14))),
% 0.61/0.81      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ X0)
% 0.61/0.81          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.81  thf(t4_subset_1, axiom,
% 0.61/0.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.61/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.61/0.81  thf(d7_tex_2, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( l1_pre_topc @ A ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81           ( ( v3_tex_2 @ B @ A ) <=>
% 0.61/0.81             ( ( v2_tex_2 @ B @ A ) & 
% 0.61/0.81               ( ![C:$i]:
% 0.61/0.81                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.81                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.81                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.61/0.81          | ~ (v3_tex_2 @ X25 @ X26)
% 0.61/0.81          | ~ (v2_tex_2 @ X27 @ X26)
% 0.61/0.81          | ~ (r1_tarski @ X25 @ X27)
% 0.61/0.81          | ((X25) = (X27))
% 0.61/0.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.61/0.81          | ~ (l1_pre_topc @ X26))),
% 0.61/0.81      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.81          | ((k1_xboole_0) = (X1))
% 0.61/0.81          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.61/0.81          | ~ (v2_tex_2 @ X1 @ X0)
% 0.61/0.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.61/0.81  thf('23', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.61/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.81          | ((k1_xboole_0) = (X1))
% 0.61/0.81          | ~ (v2_tex_2 @ X1 @ X0)
% 0.61/0.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.61/0.81      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.81          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.61/0.81          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.61/0.81          | ~ (l1_pre_topc @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['19', '24'])).
% 0.61/0.81  thf(t1_boole, axiom,
% 0.61/0.81    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.81  thf('26', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.61/0.81      inference('cnf', [status(esa)], [t1_boole])).
% 0.61/0.81  thf(t49_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.61/0.81  thf('28', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.81          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0))),
% 0.61/0.81      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | (v2_struct_0 @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.81          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['16', '29'])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.81          | (v2_struct_0 @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['30'])).
% 0.61/0.81  thf('32', plain,
% 0.61/0.81      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.61/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.81        | (v2_struct_0 @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['5', '31'])).
% 0.61/0.81  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.61/0.81  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.61/0.81      inference('clc', [status(thm)], ['35', '36'])).
% 0.61/0.81  thf(rc7_pre_topc, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.81       ( ?[B:$i]:
% 0.61/0.81         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.61/0.81           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.61/0.81  thf('38', plain,
% 0.61/0.81      (![X22 : $i]:
% 0.61/0.81         ((m1_subset_1 @ (sk_B_2 @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.61/0.81          | ~ (l1_pre_topc @ X22)
% 0.61/0.81          | ~ (v2_pre_topc @ X22)
% 0.61/0.81          | (v2_struct_0 @ X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.61/0.81  thf(cc1_subset_1, axiom,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( v1_xboole_0 @ A ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.61/0.81          | (v1_xboole_0 @ X15)
% 0.61/0.81          | ~ (v1_xboole_0 @ X16))),
% 0.61/0.81      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.61/0.81  thf('40', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((v2_struct_0 @ X0)
% 0.61/0.81          | ~ (v2_pre_topc @ X0)
% 0.61/0.81          | ~ (l1_pre_topc @ X0)
% 0.61/0.81          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.61/0.81          | (v1_xboole_0 @ (sk_B_2 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 0.61/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.81        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.81        | (v2_struct_0 @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['37', '40'])).
% 0.61/0.81  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('44', plain, (((v1_xboole_0 @ (sk_B_2 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.61/0.81  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('46', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.61/0.81      inference('clc', [status(thm)], ['44', '45'])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (![X22 : $i]:
% 0.61/0.81         (~ (v1_xboole_0 @ (sk_B_2 @ X22))
% 0.61/0.81          | ~ (l1_pre_topc @ X22)
% 0.61/0.81          | ~ (v2_pre_topc @ X22)
% 0.61/0.81          | (v2_struct_0 @ X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.81  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 0.61/0.81      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.61/0.81  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
