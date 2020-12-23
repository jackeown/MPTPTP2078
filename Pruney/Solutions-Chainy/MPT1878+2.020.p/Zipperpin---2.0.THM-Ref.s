%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jMcATSbKGf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 135 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  615 (1092 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_2 ),
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
    sk_B_2 = k1_xboole_0 ),
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

thf(rc1_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X6 ) )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jMcATSbKGf
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 154 iterations in 0.137s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.60  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.38/0.60  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.60  thf(t46_tex_2, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( v1_xboole_0 @ B ) & 
% 0.38/0.60             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.60           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.60            ( l1_pre_topc @ A ) ) =>
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ( ( v1_xboole_0 @ B ) & 
% 0.38/0.60                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.60              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.38/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(l13_xboole_0, axiom,
% 0.38/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.60  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['1', '4'])).
% 0.38/0.60  thf(d1_xboole_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.60  thf(rc1_subset_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.60       ( ?[B:$i]:
% 0.38/0.60         ( ( ~( v1_xboole_0 @ B ) ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X6 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (sk_B_1 @ X6) @ (k1_zfmisc_1 @ X6))
% 0.38/0.60          | (v1_xboole_0 @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.38/0.60  thf(t4_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.60         (~ (r2_hidden @ X8 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.38/0.60          | (m1_subset_1 @ X8 @ X10))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0)
% 0.38/0.60          | (m1_subset_1 @ X1 @ X0)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.38/0.60          | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ X0)
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X6 : $i]: (~ (v1_xboole_0 @ (sk_B_1 @ X6)) | (v1_xboole_0 @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.38/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.60       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X15)
% 0.38/0.60          | ~ (m1_subset_1 @ X16 @ X15)
% 0.38/0.60          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0)
% 0.38/0.60          | ((k6_domain_1 @ X0 @ (sk_B @ (sk_B_1 @ X0)))
% 0.38/0.60              = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k6_domain_1 @ X0 @ (sk_B @ (sk_B_1 @ X0)))
% 0.38/0.60            = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.38/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf(t36_tex_2, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.60           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.38/0.60          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.38/0.60          | ~ (l1_pre_topc @ X21)
% 0.38/0.60          | ~ (v2_pre_topc @ X21)
% 0.38/0.60          | (v2_struct_0 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v2_tex_2 @ 
% 0.38/0.60             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.38/0.60              (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))) @ 
% 0.38/0.60             X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))) @ X0)
% 0.38/0.60          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['15', '18'])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.60          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))) @ 
% 0.38/0.60             X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k6_domain_1 @ X0 @ (sk_B @ (sk_B_1 @ X0)))
% 0.38/0.60            = (k1_tarski @ (sk_B @ (sk_B_1 @ X0))))
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.38/0.60      inference('clc', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf(dt_k6_domain_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.60       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X13)
% 0.38/0.60          | ~ (m1_subset_1 @ X14 @ X13)
% 0.38/0.60          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0)
% 0.38/0.60          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.38/0.60             (k1_zfmisc_1 @ X0))
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.38/0.60           (k1_zfmisc_1 @ X0))
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.38/0.60           (k1_zfmisc_1 @ X0))
% 0.38/0.60          | (v1_xboole_0 @ X0)
% 0.38/0.60          | (v1_xboole_0 @ X0))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ X0)
% 0.38/0.60          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.38/0.60             (k1_zfmisc_1 @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.60  thf(t4_subset_1, axiom,
% 0.38/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.60  thf(d7_tex_2, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_pre_topc @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60           ( ( v3_tex_2 @ B @ A ) <=>
% 0.38/0.60             ( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.60               ( ![C:$i]:
% 0.38/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.60                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.60                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.60          | ~ (v3_tex_2 @ X17 @ X18)
% 0.38/0.60          | ~ (v2_tex_2 @ X19 @ X18)
% 0.38/0.60          | ~ (r1_tarski @ X17 @ X19)
% 0.38/0.60          | ((X17) = (X19))
% 0.38/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.60          | ~ (l1_pre_topc @ X18))),
% 0.38/0.60      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ((k1_xboole_0) = (X1))
% 0.38/0.60          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.38/0.60          | ~ (v2_tex_2 @ X1 @ X0)
% 0.38/0.60          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.60  thf('31', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.60          | ((k1_xboole_0) = (X1))
% 0.38/0.60          | ~ (v2_tex_2 @ X1 @ X0)
% 0.38/0.60          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.60          | ~ (v2_tex_2 @ 
% 0.38/0.60               (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))) @ X0)
% 0.38/0.60          | ((k1_xboole_0)
% 0.38/0.60              = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))))
% 0.38/0.60          | ~ (l1_pre_topc @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '32'])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | ((k1_xboole_0)
% 0.38/0.60              = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))))
% 0.38/0.60          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.60          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.38/0.60          | ((k1_xboole_0)
% 0.38/0.60              = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ X0)))))
% 0.38/0.60          | (v2_struct_0 @ X0)
% 0.38/0.60          | ~ (v2_pre_topc @ X0)
% 0.38/0.60          | ~ (l1_pre_topc @ X0)
% 0.38/0.60          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.60        | (v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k1_xboole_0)
% 0.38/0.60            = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['5', '35'])).
% 0.38/0.60  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.60        | (v2_struct_0 @ sk_A)
% 0.38/0.60        | ((k1_xboole_0)
% 0.38/0.60            = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.38/0.60  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (sk_B_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.60        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('clc', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.38/0.60  thf('42', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.60  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.60  thf('45', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf(fc2_struct_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (![X12 : $i]:
% 0.38/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.38/0.60          | ~ (l1_struct_0 @ X12)
% 0.38/0.60          | (v2_struct_0 @ X12))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.60  thf('47', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_l1_pre_topc, axiom,
% 0.38/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.60  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.60  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['47', '50'])).
% 0.38/0.60  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
