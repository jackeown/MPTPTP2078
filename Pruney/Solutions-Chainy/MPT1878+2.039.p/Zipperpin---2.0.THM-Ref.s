%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MTIrvUoTk9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 125 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  604 ( 976 expanded)
%              Number of equality atoms :   47 (  66 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
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

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X23 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MTIrvUoTk9
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.09/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.09/1.31  % Solved by: fo/fo7.sh
% 1.09/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.31  % done 650 iterations in 0.861s
% 1.09/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.09/1.31  % SZS output start Refutation
% 1.09/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.09/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.09/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.09/1.31  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.09/1.31  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.09/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.09/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.09/1.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.09/1.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.09/1.31  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.09/1.31  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.09/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.09/1.31  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.09/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.09/1.31  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.09/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.09/1.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.09/1.31  thf(sk_B_type, type, sk_B: $i > $i).
% 1.09/1.31  thf(t46_tex_2, conjecture,
% 1.09/1.31    (![A:$i]:
% 1.09/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.31       ( ![B:$i]:
% 1.09/1.31         ( ( ( v1_xboole_0 @ B ) & 
% 1.09/1.31             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.09/1.31           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.09/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.31    (~( ![A:$i]:
% 1.09/1.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.09/1.31            ( l1_pre_topc @ A ) ) =>
% 1.09/1.31          ( ![B:$i]:
% 1.09/1.31            ( ( ( v1_xboole_0 @ B ) & 
% 1.09/1.31                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.09/1.31              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 1.09/1.31    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 1.09/1.31  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf(l13_xboole_0, axiom,
% 1.09/1.31    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.09/1.31  thf('1', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.09/1.31  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf('4', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.09/1.31  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['3', '4'])).
% 1.09/1.31  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.09/1.31      inference('demod', [status(thm)], ['2', '5'])).
% 1.09/1.31  thf('7', plain,
% 1.09/1.31      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('sup+', [status(thm)], ['1', '6'])).
% 1.09/1.31  thf(t29_mcart_1, axiom,
% 1.09/1.31    (![A:$i]:
% 1.09/1.31     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.09/1.31          ( ![B:$i]:
% 1.09/1.31            ( ~( ( r2_hidden @ B @ A ) & 
% 1.09/1.31                 ( ![C:$i,D:$i,E:$i]:
% 1.09/1.31                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.09/1.31                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 1.09/1.31  thf('8', plain,
% 1.09/1.31      (![X11 : $i]:
% 1.09/1.31         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 1.09/1.31      inference('cnf', [status(esa)], [t29_mcart_1])).
% 1.09/1.31  thf(t1_subset, axiom,
% 1.09/1.31    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.09/1.31  thf('9', plain,
% 1.09/1.31      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 1.09/1.31      inference('cnf', [status(esa)], [t1_subset])).
% 1.09/1.31  thf('10', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.09/1.31  thf(redefinition_k6_domain_1, axiom,
% 1.09/1.31    (![A:$i,B:$i]:
% 1.09/1.31     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.09/1.31       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.09/1.31  thf('11', plain,
% 1.09/1.31      (![X19 : $i, X20 : $i]:
% 1.09/1.31         ((v1_xboole_0 @ X19)
% 1.09/1.31          | ~ (m1_subset_1 @ X20 @ X19)
% 1.09/1.31          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 1.09/1.31      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.09/1.31  thf('12', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((X0) = (k1_xboole_0))
% 1.09/1.31          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.09/1.31          | (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['10', '11'])).
% 1.09/1.31  thf('13', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.09/1.31  thf('14', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.09/1.31          | ((X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('clc', [status(thm)], ['12', '13'])).
% 1.09/1.31  thf('15', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.09/1.31  thf(t36_tex_2, axiom,
% 1.09/1.31    (![A:$i]:
% 1.09/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.09/1.31       ( ![B:$i]:
% 1.09/1.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.09/1.31           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.09/1.31  thf('16', plain,
% 1.09/1.31      (![X24 : $i, X25 : $i]:
% 1.09/1.31         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 1.09/1.31          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 1.09/1.31          | ~ (l1_pre_topc @ X25)
% 1.09/1.31          | ~ (v2_pre_topc @ X25)
% 1.09/1.31          | (v2_struct_0 @ X25))),
% 1.09/1.31      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.09/1.31  thf('17', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | (v2_struct_0 @ X0)
% 1.09/1.31          | ~ (v2_pre_topc @ X0)
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | (v2_tex_2 @ 
% 1.09/1.31             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 1.09/1.31             X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['15', '16'])).
% 1.09/1.31  thf('18', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.09/1.31          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | ~ (v2_pre_topc @ X0)
% 1.09/1.31          | (v2_struct_0 @ X0)
% 1.09/1.31          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('sup+', [status(thm)], ['14', '17'])).
% 1.09/1.31  thf('19', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         ((v2_struct_0 @ X0)
% 1.09/1.31          | ~ (v2_pre_topc @ X0)
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 1.09/1.31      inference('simplify', [status(thm)], ['18'])).
% 1.09/1.31  thf('20', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.09/1.31          | ((X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('clc', [status(thm)], ['12', '13'])).
% 1.09/1.31  thf('21', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.09/1.31  thf(dt_k6_domain_1, axiom,
% 1.09/1.31    (![A:$i,B:$i]:
% 1.09/1.31     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.09/1.31       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.09/1.31  thf('22', plain,
% 1.09/1.31      (![X17 : $i, X18 : $i]:
% 1.09/1.31         ((v1_xboole_0 @ X17)
% 1.09/1.31          | ~ (m1_subset_1 @ X18 @ X17)
% 1.09/1.31          | (m1_subset_1 @ (k6_domain_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17)))),
% 1.09/1.31      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.09/1.31  thf('23', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((X0) = (k1_xboole_0))
% 1.09/1.31          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 1.09/1.31             (k1_zfmisc_1 @ X0))
% 1.09/1.31          | (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['21', '22'])).
% 1.09/1.31  thf('24', plain,
% 1.09/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.09/1.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.09/1.31  thf('25', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.09/1.31          | ((X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('clc', [status(thm)], ['23', '24'])).
% 1.09/1.31  thf('26', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 1.09/1.31          | ((X0) = (k1_xboole_0))
% 1.09/1.31          | ((X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('sup+', [status(thm)], ['20', '25'])).
% 1.09/1.31  thf('27', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((X0) = (k1_xboole_0))
% 1.09/1.31          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 1.09/1.31      inference('simplify', [status(thm)], ['26'])).
% 1.09/1.31  thf(t4_subset_1, axiom,
% 1.09/1.31    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.09/1.31  thf('28', plain,
% 1.09/1.31      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 1.09/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.09/1.31  thf(d7_tex_2, axiom,
% 1.09/1.31    (![A:$i]:
% 1.09/1.31     ( ( l1_pre_topc @ A ) =>
% 1.09/1.31       ( ![B:$i]:
% 1.09/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.31           ( ( v3_tex_2 @ B @ A ) <=>
% 1.09/1.31             ( ( v2_tex_2 @ B @ A ) & 
% 1.09/1.31               ( ![C:$i]:
% 1.09/1.31                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.09/1.31                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.09/1.31                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.09/1.31  thf('29', plain,
% 1.09/1.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.09/1.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.09/1.31          | ~ (v3_tex_2 @ X21 @ X22)
% 1.09/1.31          | ~ (v2_tex_2 @ X23 @ X22)
% 1.09/1.31          | ~ (r1_tarski @ X21 @ X23)
% 1.09/1.31          | ((X21) = (X23))
% 1.09/1.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.09/1.31          | ~ (l1_pre_topc @ X22))),
% 1.09/1.31      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.09/1.31  thf('30', plain,
% 1.09/1.31      (![X0 : $i, X1 : $i]:
% 1.09/1.31         (~ (l1_pre_topc @ X0)
% 1.09/1.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.09/1.31          | ((k1_xboole_0) = (X1))
% 1.09/1.31          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 1.09/1.31          | ~ (v2_tex_2 @ X1 @ X0)
% 1.09/1.31          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['28', '29'])).
% 1.09/1.31  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.09/1.31  thf('31', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 1.09/1.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.09/1.31  thf('32', plain,
% 1.09/1.31      (![X0 : $i, X1 : $i]:
% 1.09/1.31         (~ (l1_pre_topc @ X0)
% 1.09/1.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.09/1.31          | ((k1_xboole_0) = (X1))
% 1.09/1.31          | ~ (v2_tex_2 @ X1 @ X0)
% 1.09/1.31          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 1.09/1.31      inference('demod', [status(thm)], ['30', '31'])).
% 1.09/1.31  thf('33', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.09/1.31          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.09/1.31          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 1.09/1.31          | ~ (l1_pre_topc @ X0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['27', '32'])).
% 1.09/1.31  thf(t1_boole, axiom,
% 1.09/1.31    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.09/1.31  thf('34', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 1.09/1.31      inference('cnf', [status(esa)], [t1_boole])).
% 1.09/1.31  thf(t49_zfmisc_1, axiom,
% 1.09/1.31    (![A:$i,B:$i]:
% 1.09/1.31     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.09/1.31  thf('35', plain,
% 1.09/1.31      (![X3 : $i, X4 : $i]:
% 1.09/1.31         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 1.09/1.31      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.09/1.31  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 1.09/1.31      inference('sup-', [status(thm)], ['34', '35'])).
% 1.09/1.31  thf('37', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.09/1.31          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 1.09/1.31          | ~ (l1_pre_topc @ X0))),
% 1.09/1.31      inference('simplify_reflect-', [status(thm)], ['33', '36'])).
% 1.09/1.31  thf('38', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | ~ (v2_pre_topc @ X0)
% 1.09/1.31          | (v2_struct_0 @ X0)
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.09/1.31          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('sup-', [status(thm)], ['19', '37'])).
% 1.09/1.31  thf('39', plain,
% 1.09/1.31      (![X0 : $i]:
% 1.09/1.31         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.09/1.31          | (v2_struct_0 @ X0)
% 1.09/1.31          | ~ (v2_pre_topc @ X0)
% 1.09/1.31          | ~ (l1_pre_topc @ X0)
% 1.09/1.31          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 1.09/1.31      inference('simplify', [status(thm)], ['38'])).
% 1.09/1.31  thf('40', plain,
% 1.09/1.31      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.09/1.31        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.09/1.31        | ~ (l1_pre_topc @ sk_A)
% 1.09/1.31        | ~ (v2_pre_topc @ sk_A)
% 1.09/1.31        | (v2_struct_0 @ sk_A))),
% 1.09/1.31      inference('sup-', [status(thm)], ['7', '39'])).
% 1.09/1.31  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.09/1.31  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.09/1.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.09/1.31  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf('44', plain,
% 1.09/1.31      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 1.09/1.31      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 1.09/1.31  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf('46', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 1.09/1.31      inference('clc', [status(thm)], ['44', '45'])).
% 1.09/1.31  thf(fc2_struct_0, axiom,
% 1.09/1.31    (![A:$i]:
% 1.09/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.09/1.31       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.09/1.31  thf('47', plain,
% 1.09/1.31      (![X16 : $i]:
% 1.09/1.31         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 1.09/1.31          | ~ (l1_struct_0 @ X16)
% 1.09/1.31          | (v2_struct_0 @ X16))),
% 1.09/1.31      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.09/1.31  thf('48', plain,
% 1.09/1.31      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.09/1.31        | (v2_struct_0 @ sk_A)
% 1.09/1.31        | ~ (l1_struct_0 @ sk_A))),
% 1.09/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.09/1.31  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.09/1.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.09/1.31  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.09/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.31  thf(dt_l1_pre_topc, axiom,
% 1.09/1.31    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.09/1.31  thf('51', plain,
% 1.09/1.31      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.09/1.31      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.09/1.31  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 1.09/1.31      inference('sup-', [status(thm)], ['50', '51'])).
% 1.09/1.31  thf('53', plain, ((v2_struct_0 @ sk_A)),
% 1.09/1.31      inference('demod', [status(thm)], ['48', '49', '52'])).
% 1.09/1.31  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 1.09/1.31  
% 1.09/1.31  % SZS output end Refutation
% 1.09/1.31  
% 1.09/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
