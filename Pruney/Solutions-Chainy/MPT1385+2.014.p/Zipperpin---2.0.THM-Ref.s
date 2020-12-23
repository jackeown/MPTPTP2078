%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NCxmnPo71S

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:00 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 446 expanded)
%              Number of leaves         :   28 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          : 1347 (7023 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t10_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_connsp_2 @ ( sk_C @ X22 @ X21 ) @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('3',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['6','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m2_connsp_2 @ X17 @ X16 @ X15 )
      | ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('56',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['68'])).

thf('72',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_connsp_2 @ X14 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('85',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('86',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ( m2_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('97',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['68'])).

thf('98',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['83','108'])).

thf('110',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['71','109'])).

thf('111',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('112',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['71','109','111'])).

thf('113',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','110','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','113'])).

thf('115',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['26','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NCxmnPo71S
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 20:03:30 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 156 iterations in 0.061s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.24/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.24/0.51  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.51  thf(t10_connsp_2, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.51           ( ![C:$i]:
% 0.24/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51               ( ( m2_connsp_2 @
% 0.24/0.51                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.24/0.51                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.51            ( l1_pre_topc @ A ) ) =>
% 0.24/0.51          ( ![B:$i]:
% 0.24/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.51              ( ![C:$i]:
% 0.24/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51                  ( ( m2_connsp_2 @
% 0.24/0.51                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.24/0.51                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.24/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(existence_m1_connsp_2, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X21 : $i, X22 : $i]:
% 0.24/0.51         (~ (l1_pre_topc @ X21)
% 0.24/0.51          | ~ (v2_pre_topc @ X21)
% 0.24/0.51          | (v2_struct_0 @ X21)
% 0.24/0.51          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.24/0.51          | (m1_connsp_2 @ (sk_C @ X22 @ X21) @ X21 @ X22))),
% 0.24/0.51      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.24/0.51        | (v2_struct_0 @ sk_A)
% 0.24/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.51  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.24/0.51        | (v2_struct_0 @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.24/0.51  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('8', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.24/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf('9', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.24/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(dt_m1_connsp_2, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51       ( ![C:$i]:
% 0.24/0.51         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.24/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.51         (~ (l1_pre_topc @ X18)
% 0.24/0.51          | ~ (v2_pre_topc @ X18)
% 0.24/0.51          | (v2_struct_0 @ X18)
% 0.24/0.51          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.24/0.51          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.24/0.51          | ~ (m1_connsp_2 @ X20 @ X18 @ X19))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.24/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (v2_struct_0 @ sk_A)
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.24/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (v2_struct_0 @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.24/0.51  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.24/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.24/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.24/0.51  thf(d1_connsp_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.51           ( ![C:$i]:
% 0.24/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.24/0.51                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('19', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.24/0.51          | ~ (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.24/0.51          | (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.24/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.51          | ~ (l1_pre_topc @ X13)
% 0.24/0.51          | ~ (v2_pre_topc @ X13)
% 0.24/0.51          | (v2_struct_0 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.24/0.51  thf('20', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.24/0.51          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.51  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('23', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.24/0.51          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.24/0.51  thf('24', plain,
% 0.24/0.51      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.51        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.24/0.51        | (v2_struct_0 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['8', '23'])).
% 0.24/0.51  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('26', plain,
% 0.24/0.51      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)))
% 0.24/0.51        | (v2_struct_0 @ sk_A))),
% 0.24/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.24/0.51  thf('27', plain,
% 0.24/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.24/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.24/0.51  thf(dt_k1_tops_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( l1_pre_topc @ A ) & 
% 0.24/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.51       ( m1_subset_1 @
% 0.24/0.51         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.51  thf('28', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         (~ (l1_pre_topc @ X10)
% 0.24/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.51          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.24/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.24/0.51  thf('29', plain,
% 0.24/0.51      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)) @ 
% 0.24/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.51  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('31', plain,
% 0.24/0.51      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)) @ 
% 0.24/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.24/0.51  thf(t5_subset, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.51  thf('32', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.24/0.51          | ~ (v1_xboole_0 @ X5)
% 0.24/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.51  thf('33', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.51  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.51  thf('35', plain,
% 0.24/0.51      (![X8 : $i, X9 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X8)
% 0.24/0.51          | ~ (m1_subset_1 @ X9 @ X8)
% 0.24/0.51          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.24/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.51  thf('36', plain,
% 0.24/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.51  thf('37', plain,
% 0.24/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.24/0.51        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('38', plain,
% 0.24/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('split', [status(esa)], ['37'])).
% 0.24/0.51  thf('39', plain,
% 0.24/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup+', [status(thm)], ['36', '38'])).
% 0.24/0.51  thf('40', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('41', plain,
% 0.24/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.51  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(dt_k6_domain_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.51  thf('43', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ X6)
% 0.24/0.51          | ~ (m1_subset_1 @ X7 @ X6)
% 0.24/0.51          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.24/0.51  thf('44', plain,
% 0.24/0.51      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.24/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.51  thf('45', plain,
% 0.24/0.51      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.24/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['41', '44'])).
% 0.24/0.51  thf('46', plain,
% 0.24/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.24/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.24/0.51  thf(d2_connsp_2, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.51       ( ![B:$i]:
% 0.24/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51           ( ![C:$i]:
% 0.24/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.51               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.24/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.24/0.51  thf('47', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.24/0.51          | ~ (m2_connsp_2 @ X17 @ X16 @ X15)
% 0.24/0.51          | (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.24/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.24/0.51          | ~ (l1_pre_topc @ X16)
% 0.24/0.51          | ~ (v2_pre_topc @ X16))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.24/0.51  thf('48', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.24/0.51          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.51  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('51', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.24/0.51          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.24/0.51  thf('52', plain,
% 0.24/0.51      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['40', '51'])).
% 0.24/0.51  thf('53', plain,
% 0.24/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['39', '52'])).
% 0.24/0.51  thf('54', plain,
% 0.24/0.51      ((((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.24/0.51  thf(l1_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.24/0.51  thf('55', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]:
% 0.24/0.51         ((r2_hidden @ X0 @ X1) | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.24/0.51  thf('56', plain,
% 0.24/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.24/0.51  thf('57', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('58', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.24/0.51          | ~ (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.24/0.51          | (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.24/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.51          | ~ (l1_pre_topc @ X13)
% 0.24/0.51          | ~ (v2_pre_topc @ X13)
% 0.24/0.51          | (v2_struct_0 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.24/0.51  thf('59', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.24/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.24/0.51  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('62', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.24/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.24/0.51  thf('63', plain,
% 0.24/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.24/0.51         | (v2_struct_0 @ sk_A)))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['56', '62'])).
% 0.24/0.51  thf('64', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('65', plain,
% 0.24/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.24/0.51         | (v2_struct_0 @ sk_A)))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.24/0.51  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('67', plain,
% 0.24/0.51      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('clc', [status(thm)], ['65', '66'])).
% 0.24/0.51  thf('68', plain,
% 0.24/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.24/0.51        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('69', plain,
% 0.24/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.24/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('split', [status(esa)], ['68'])).
% 0.24/0.51  thf('70', plain,
% 0.24/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['67', '69'])).
% 0.24/0.51  thf('71', plain,
% 0.24/0.51      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.24/0.51       ~
% 0.24/0.51       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.51      inference('split', [status(esa)], ['68'])).
% 0.24/0.51  thf('72', plain,
% 0.24/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('split', [status(esa)], ['37'])).
% 0.24/0.51  thf('73', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('74', plain,
% 0.24/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.24/0.51          | ~ (m1_connsp_2 @ X14 @ X13 @ X12)
% 0.24/0.51          | (r2_hidden @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.24/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.51          | ~ (l1_pre_topc @ X13)
% 0.24/0.51          | ~ (v2_pre_topc @ X13)
% 0.24/0.51          | (v2_struct_0 @ X13))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.24/0.51  thf('75', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.24/0.51  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('78', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v2_struct_0 @ sk_A)
% 0.24/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.24/0.51  thf('79', plain,
% 0.24/0.51      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['72', '78'])).
% 0.24/0.51  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('81', plain,
% 0.24/0.51      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.24/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['79', '80'])).
% 0.24/0.51  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('83', plain,
% 0.24/0.51      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.24/0.51  thf('84', plain,
% 0.24/0.51      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.24/0.51  thf('85', plain,
% 0.24/0.51      (![X0 : $i, X2 : $i]:
% 0.24/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X2) | ~ (r2_hidden @ X0 @ X2))),
% 0.24/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.24/0.51  thf('86', plain,
% 0.24/0.51      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.24/0.51  thf('87', plain,
% 0.24/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.24/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.24/0.51  thf('88', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.24/0.51          | ~ (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.24/0.51          | (m2_connsp_2 @ X17 @ X16 @ X15)
% 0.24/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.24/0.51          | ~ (l1_pre_topc @ X16)
% 0.24/0.51          | ~ (v2_pre_topc @ X16))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.24/0.51  thf('89', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.24/0.51  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('92', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.24/0.51      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.24/0.51  thf('93', plain,
% 0.24/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['86', '92'])).
% 0.24/0.51  thf('94', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('95', plain,
% 0.24/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('demod', [status(thm)], ['93', '94'])).
% 0.24/0.51  thf('96', plain,
% 0.24/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.51  thf('97', plain,
% 0.24/0.51      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.24/0.51         <= (~
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('split', [status(esa)], ['68'])).
% 0.24/0.51  thf('98', plain,
% 0.24/0.51      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (~
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.24/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.24/0.51  thf('99', plain,
% 0.24/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.51         <= (~
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.24/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['95', '98'])).
% 0.24/0.51  thf('100', plain,
% 0.24/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51         <= (~
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.24/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['99'])).
% 0.24/0.51  thf('101', plain,
% 0.24/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('102', plain,
% 0.24/0.51      (![X10 : $i, X11 : $i]:
% 0.24/0.51         (~ (l1_pre_topc @ X10)
% 0.24/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.51          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.24/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.24/0.51  thf('103', plain,
% 0.24/0.51      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.24/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.24/0.51  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('105', plain,
% 0.24/0.51      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.24/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['103', '104'])).
% 0.24/0.51  thf('106', plain,
% 0.24/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.24/0.51          | ~ (v1_xboole_0 @ X5)
% 0.24/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.51  thf('107', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['105', '106'])).
% 0.24/0.51  thf('108', plain,
% 0.24/0.51      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.24/0.51         <= (~
% 0.24/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.24/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['100', '107'])).
% 0.24/0.51  thf('109', plain,
% 0.24/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.24/0.51       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['83', '108'])).
% 0.24/0.51  thf('110', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['71', '109'])).
% 0.24/0.51  thf('111', plain,
% 0.24/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.24/0.51       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.24/0.51      inference('split', [status(esa)], ['37'])).
% 0.24/0.51  thf('112', plain,
% 0.24/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.24/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.51      inference('sat_resolution*', [status(thm)], ['71', '109', '111'])).
% 0.24/0.51  thf('113', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.24/0.51      inference('simpl_trail', [status(thm)], ['70', '110', '112'])).
% 0.24/0.51  thf('114', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (sk_C @ sk_B @ sk_A)))),
% 0.24/0.51      inference('demod', [status(thm)], ['33', '113'])).
% 0.24/0.51  thf('115', plain, ((v2_struct_0 @ sk_A)),
% 0.24/0.51      inference('clc', [status(thm)], ['26', '114'])).
% 0.24/0.51  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
