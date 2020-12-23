%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dHuHQ7NDyH

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:29 EST 2020

% Result     : Theorem 33.40s
% Output     : Refutation 33.40s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 935 expanded)
%              Number of leaves         :   45 ( 276 expanded)
%              Depth                    :   32
%              Number of atoms          : 1854 (10259 expanded)
%              Number of equality atoms :   84 ( 195 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('3',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( sk_D @ X31 @ X29 @ X30 ) )
        = ( k1_tarski @ X31 ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_4 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_4 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_zfmisc_1 @ sk_B_4 )
    | ( v2_tex_2 @ sk_B_4 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B_4 @ sk_A )
   <= ( v2_tex_2 @ sk_B_4 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_4 )
    | ~ ( v2_tex_2 @ sk_B_4 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_4 )
    | ~ ( v2_tex_2 @ sk_B_4 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ X5 )
      | ( X5
        = ( k6_domain_1 @ X5 @ ( sk_B @ X5 ) ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('13',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ X5 )
      | ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( v1_zfmisc_1 @ sk_B_4 )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ X5 )
      | ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( m1_subset_1 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ~ ( v1_zfmisc_1 @ sk_B_4 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_4 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_4 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_4 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('32',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_4 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_4 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_4 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_4 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_4 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_4 ) ) @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_4 ) ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,
    ( ( ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ( v1_xboole_0 @ sk_B_4 )
      | ~ ( v1_zfmisc_1 @ sk_B_4 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup+',[status(thm)],['18','41'])).

thf('43',plain,
    ( ( v1_zfmisc_1 @ sk_B_4 )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ( ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ( v1_xboole_0 @ sk_B_4 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ sk_B_4 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_B_4 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_4 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('56',plain,
    ( ( v2_tex_2 @ sk_B_4 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_tex_2 @ sk_B_4 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(split,[status(esa)],['8'])).

thf('58',plain,(
    v2_tex_2 @ sk_B_4 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['11','56','57'])).

thf('59',plain,(
    v2_tex_2 @ sk_B_4 @ sk_A ),
    inference(simpl_trail,[status(thm)],['9','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_4 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_4 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X21 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_4 )
      = ( k3_xboole_0 @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B_4 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_4 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( ( k3_xboole_0 @ sk_B_4 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','59','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_4 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ( ( k3_xboole_0 @ sk_B_4 @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) )
      = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ) ),
    inference('sup-',[status(thm)],['2','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) )
    = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X31 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v2_tex_2 @ sk_B_4 @ sk_A ),
    inference(simpl_trail,[status(thm)],['9','58'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ( m1_subset_1 @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf(t20_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v2_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( v3_pre_topc @ B @ A )
                & ( B != k1_xboole_0 )
                & ( B
                 != ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_tdlat_3 @ X22 )
      | ( X23
        = ( u1_struct_0 @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t20_tdlat_3])).

thf('88',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ sk_A )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ sk_A )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('95',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    r1_tarski @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('97',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_4 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B_4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('101',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B_4 )
      = ( k3_xboole_0 @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('104',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B_4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_pre_topc @ ( sk_D @ X31 @ X29 @ X30 ) @ X30 )
      | ~ ( r2_hidden @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ sk_B_4 @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ X0 @ ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,(
    v2_tex_2 @ sk_B_4 @ sk_A ),
    inference(simpl_trail,[status(thm)],['9','58'])).

thf('112',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_4 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('113',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_4 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_4 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_4 @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_4 )
    | ( v3_pre_topc @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['93','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','119'])).

thf('121',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A ) )
    = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('122',plain,
    ( ( ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k3_xboole_0 @ sk_B_4 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_4 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('124',plain,
    ( ( sk_B_4
      = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('126',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('129',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ X0 )
        = ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) )
        = ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_4 ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('144',plain,
    ( ( k3_xboole_0 @ ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) )
    = ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('146',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) )
    = ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) )
      = ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( v1_xboole_0 @ sk_B_4 ) ),
    inference('sup+',[status(thm)],['127','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('149',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) )
      = ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( v1_xboole_0 @ sk_B_4 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) )
    = ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B_4 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_4 ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('167',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('169',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) @ ( u1_struct_0 @ sk_A ) )
    = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k6_domain_1 @ sk_B_4 @ ( sk_B_1 @ sk_B_4 ) )
    = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference('sup+',[status(thm)],['151','169'])).

thf('171',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
       != ( k6_domain_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( v1_zfmisc_1 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('172',plain,
    ( ( sk_B_4
     != ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( v1_xboole_0 @ sk_B_4 )
    | ( v1_zfmisc_1 @ sk_B_4 )
    | ~ ( m1_subset_1 @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('174',plain,
    ( ( sk_B_4
     != ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) )
    | ( v1_xboole_0 @ sk_B_4 )
    | ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v1_xboole_0 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_zfmisc_1 @ sk_B_4 )
    | ( sk_B_4
     != ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_4 )
   <= ~ ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(split,[status(esa)],['10'])).

thf('178',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference('sat_resolution*',[status(thm)],['11','56'])).

thf('179',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_4 ) ),
    inference(simpl_trail,[status(thm)],['177','178'])).

thf('180',plain,(
    sk_B_4
 != ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(clc,[status(thm)],['176','179'])).

thf('181',plain,
    ( ( sk_D @ ( sk_B_1 @ sk_B_4 ) @ sk_B_4 @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['124','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('184',plain,(
    ! [X26: $i] :
      ( ( k3_xboole_0 @ X26 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( sk_B_1 @ sk_B_4 ) ) ),
    inference(demod,[status(thm)],['73','181','182','185'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('187',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['188','189'])).


%------------------------------------------------------------------------------
