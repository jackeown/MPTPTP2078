%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5of21YIEzY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 410 expanded)
%              Number of leaves         :   29 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          : 1355 (6392 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( m1_connsp_2 @ ( sk_C @ X26 @ X25 ) @ X25 @ X26 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X21 @ X19 @ X20 ) ) ),
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

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_connsp_2 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
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
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('48',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf('68',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_connsp_2 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('93',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('104',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['60'])).

thf('105',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','111'])).

thf('113',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['67','112'])).

thf('114',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('115',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['67','112','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['66','113','115'])).

thf('117',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['26','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5of21YIEzY
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 148 iterations in 0.062s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t10_connsp_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( m2_connsp_2 @
% 0.20/0.51                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.20/0.51                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                  ( ( m2_connsp_2 @
% 0.20/0.51                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.20/0.51                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(existence_m1_connsp_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X25)
% 0.20/0.51          | ~ (v2_pre_topc @ X25)
% 0.20/0.51          | (v2_struct_0 @ X25)
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.20/0.51          | (m1_connsp_2 @ (sk_C @ X26 @ X25) @ X25 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.51  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_connsp_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X19)
% 0.20/0.51          | ~ (v2_pre_topc @ X19)
% 0.20/0.51          | (v2_struct_0 @ X19)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.20/0.51          | (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.51          | ~ (m1_connsp_2 @ X21 @ X19 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.51  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf(t6_connsp_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.51          | ~ (m1_connsp_2 @ X27 @ X28 @ X29)
% 0.20/0.51          | (r2_hidden @ X29 @ X27)
% 0.20/0.51          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.20/0.51          | ~ (l1_pre_topc @ X28)
% 0.20/0.51          | ~ (v2_pre_topc @ X28)
% 0.20/0.51          | (v2_struct_0 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.51          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.51          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '23'])).
% 0.20/0.51  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.51          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['29', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((r2_hidden @ X6 @ X7)
% 0.20/0.51          | (v1_xboole_0 @ X7)
% 0.20/0.51          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf(t63_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.20/0.51          | ~ (r2_hidden @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf(d2_connsp_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.20/0.51          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (l1_pre_topc @ X17)
% 0.20/0.51          | ~ (v2_pre_topc @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.51          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.51          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.51  thf(l1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X2) | ~ (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d1_connsp_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.51                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.20/0.51          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.51          | ~ (l1_pre_topc @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '54'])).
% 0.20/0.51  thf('56', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf(t5_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.51          | ~ (v1_xboole_0 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~
% 0.20/0.51       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['60'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['30'])).
% 0.20/0.51  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.51          | ~ (m1_connsp_2 @ X27 @ X28 @ X29)
% 0.20/0.51          | (r2_hidden @ X29 @ X27)
% 0.20/0.51          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.20/0.51          | ~ (l1_pre_topc @ X28)
% 0.20/0.51          | ~ (v2_pre_topc @ X28)
% 0.20/0.51          | (v2_struct_0 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.51  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51        | (r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['69', '75'])).
% 0.20/0.51  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C_1) | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C_1))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '78'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['30'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.20/0.51          | (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.51          | ~ (l1_pre_topc @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.51  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['80', '86'])).
% 0.20/0.51  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.51  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (![X1 : $i, X3 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.20/0.51          | (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (l1_pre_topc @ X17)
% 0.20/0.51          | ~ (v2_pre_topc @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.51  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '99'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['100', '101'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['60'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['102', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['106'])).
% 0.20/0.51  thf('108', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X8 @ X9)
% 0.20/0.51          | ~ (v1_xboole_0 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.20/0.51         <= (~
% 0.20/0.51             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.51             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['107', '110'])).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.20/0.51       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '111'])).
% 0.20/0.51  thf('113', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['67', '112'])).
% 0.20/0.51  thf('114', plain,
% 0.20/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.20/0.51       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['30'])).
% 0.20/0.51  thf('115', plain,
% 0.20/0.51      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['67', '112', '114'])).
% 0.20/0.51  thf('116', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['66', '113', '115'])).
% 0.20/0.51  thf('117', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['26', '116'])).
% 0.20/0.51  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
