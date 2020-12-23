%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3g6n8EzAK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 282 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  656 (5365 expanded)
%              Number of equality atoms :    9 ( 115 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X21 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['9','10'])).

thf('23',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('37',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28','40','45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L3g6n8EzAK
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 390 iterations in 0.315s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.76  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.57/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.76  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.57/0.76  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.57/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.76  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.57/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.57/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.57/0.76  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.57/0.76  thf(t58_tex_2, conjecture,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.57/0.76         ( l1_pre_topc @ A ) ) =>
% 0.57/0.76       ( ![B:$i]:
% 0.57/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.76           ( ( ![C:$i]:
% 0.57/0.76               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.76                 ( ( r2_hidden @ C @ B ) =>
% 0.57/0.76                   ( ( k9_subset_1 @
% 0.57/0.76                       ( u1_struct_0 @ A ) @ B @ 
% 0.57/0.76                       ( k2_pre_topc @
% 0.57/0.76                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.57/0.76                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.57/0.76             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i]:
% 0.57/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.76            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.76          ( ![B:$i]:
% 0.57/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.76              ( ( ![C:$i]:
% 0.57/0.76                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.76                    ( ( r2_hidden @ C @ B ) =>
% 0.57/0.76                      ( ( k9_subset_1 @
% 0.57/0.76                          ( u1_struct_0 @ A ) @ B @ 
% 0.57/0.76                          ( k2_pre_topc @
% 0.57/0.76                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.57/0.76                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.57/0.76                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.57/0.76  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('1', plain,
% 0.57/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(t57_tex_2, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.57/0.76         ( l1_pre_topc @ A ) ) =>
% 0.57/0.76       ( ![B:$i]:
% 0.57/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.76           ( ( ![C:$i]:
% 0.57/0.76               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.76                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.57/0.76                      ( ![D:$i]:
% 0.57/0.76                        ( ( m1_subset_1 @
% 0.57/0.76                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.76                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.57/0.76                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.57/0.76                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.57/0.76             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.57/0.76  thf('2', plain,
% 0.57/0.76      (![X18 : $i, X19 : $i]:
% 0.57/0.76         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.57/0.76          | (v2_tex_2 @ X18 @ X19)
% 0.57/0.76          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ X18)
% 0.57/0.76          | ~ (l1_pre_topc @ X19)
% 0.57/0.76          | ~ (v3_tdlat_3 @ X19)
% 0.57/0.76          | ~ (v2_pre_topc @ X19)
% 0.57/0.76          | (v2_struct_0 @ X19))),
% 0.57/0.76      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (((v2_struct_0 @ sk_A)
% 0.57/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.76        | ~ (v3_tdlat_3 @ sk_A)
% 0.57/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.76        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.57/0.76        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.76  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('5', plain, ((v3_tdlat_3 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (((v2_struct_0 @ sk_A)
% 0.57/0.76        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.57/0.76        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.57/0.76      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.57/0.76  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('9', plain,
% 0.57/0.76      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.57/0.76        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.57/0.76      inference('clc', [status(thm)], ['7', '8'])).
% 0.57/0.76  thf('10', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('11', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.57/0.76      inference('clc', [status(thm)], ['9', '10'])).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(t3_subset, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.76  thf('13', plain,
% 0.57/0.76      (![X9 : $i, X10 : $i]:
% 0.57/0.76         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.76  thf('14', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.76  thf(d3_tarski, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X3 @ X4)
% 0.57/0.76          | (r2_hidden @ X3 @ X5)
% 0.57/0.76          | ~ (r1_tarski @ X4 @ X5))),
% 0.57/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['11', '16'])).
% 0.57/0.76  thf(t1_subset, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.57/0.76      inference('cnf', [status(esa)], [t1_subset])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.76  thf('20', plain,
% 0.57/0.76      (![X21 : $i]:
% 0.57/0.76         (~ (r2_hidden @ X21 @ sk_B_1)
% 0.57/0.76          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.57/0.76              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X21)))
% 0.57/0.76              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X21))
% 0.57/0.76          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.57/0.76          (k2_pre_topc @ sk_A @ 
% 0.57/0.76           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.57/0.76          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.57/0.76        | ~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['19', '20'])).
% 0.57/0.76  thf('22', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.57/0.76      inference('clc', [status(thm)], ['9', '10'])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.57/0.76         (k2_pre_topc @ sk_A @ 
% 0.57/0.76          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.57/0.76         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['21', '22'])).
% 0.57/0.76  thf('24', plain,
% 0.57/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.76         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.57/0.76          | (v2_tex_2 @ X18 @ X19)
% 0.57/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.57/0.76          | ~ (v4_pre_topc @ X20 @ X19)
% 0.57/0.76          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20)
% 0.57/0.76              != (k6_domain_1 @ (u1_struct_0 @ X19) @ (sk_C_1 @ X18 @ X19)))
% 0.57/0.76          | ~ (l1_pre_topc @ X19)
% 0.57/0.76          | ~ (v3_tdlat_3 @ X19)
% 0.57/0.76          | ~ (v2_pre_topc @ X19)
% 0.57/0.76          | (v2_struct_0 @ X19))),
% 0.57/0.76      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.57/0.76          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.57/0.76        | (v2_struct_0 @ sk_A)
% 0.57/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.76        | ~ (v3_tdlat_3 @ sk_A)
% 0.57/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.76        | ~ (v4_pre_topc @ 
% 0.57/0.76             (k2_pre_topc @ sk_A @ 
% 0.57/0.76              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76             sk_A)
% 0.57/0.76        | ~ (m1_subset_1 @ 
% 0.57/0.76             (k2_pre_topc @ sk_A @ 
% 0.57/0.76              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.76        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.57/0.76        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.57/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.57/0.76  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('27', plain, ((v3_tdlat_3 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('29', plain,
% 0.57/0.76      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.57/0.76  thf(dt_k6_domain_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.57/0.76       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.57/0.76  thf('30', plain,
% 0.57/0.76      (![X14 : $i, X15 : $i]:
% 0.57/0.76         ((v1_xboole_0 @ X14)
% 0.57/0.76          | ~ (m1_subset_1 @ X15 @ X14)
% 0.57/0.76          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.57/0.76      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.57/0.76  thf('31', plain,
% 0.57/0.76      (((m1_subset_1 @ 
% 0.57/0.76         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.57/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.76  thf('32', plain,
% 0.57/0.76      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['11', '16'])).
% 0.57/0.76  thf(d1_xboole_0, axiom,
% 0.57/0.76    (![A:$i]:
% 0.57/0.76     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.57/0.76  thf('33', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.57/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.76  thf('34', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.57/0.76  thf('35', plain,
% 0.57/0.76      ((m1_subset_1 @ 
% 0.57/0.76        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.57/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('clc', [status(thm)], ['31', '34'])).
% 0.57/0.76  thf(fc1_tops_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.57/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.76       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.57/0.76  thf('36', plain,
% 0.57/0.76      (![X16 : $i, X17 : $i]:
% 0.57/0.76         (~ (l1_pre_topc @ X16)
% 0.57/0.76          | ~ (v2_pre_topc @ X16)
% 0.57/0.76          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.57/0.76          | (v4_pre_topc @ (k2_pre_topc @ X16 @ X17) @ X16))),
% 0.57/0.76      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.57/0.76  thf('37', plain,
% 0.57/0.76      (((v4_pre_topc @ 
% 0.57/0.76         (k2_pre_topc @ sk_A @ 
% 0.57/0.76          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76         sk_A)
% 0.57/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.57/0.76  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('40', plain,
% 0.57/0.76      ((v4_pre_topc @ 
% 0.57/0.76        (k2_pre_topc @ sk_A @ 
% 0.57/0.76         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76        sk_A)),
% 0.57/0.76      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.57/0.76  thf('41', plain,
% 0.57/0.76      ((m1_subset_1 @ 
% 0.57/0.76        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.57/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('clc', [status(thm)], ['31', '34'])).
% 0.57/0.76  thf(dt_k2_pre_topc, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( l1_pre_topc @ A ) & 
% 0.57/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.76       ( m1_subset_1 @
% 0.57/0.76         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.57/0.76  thf('42', plain,
% 0.57/0.76      (![X12 : $i, X13 : $i]:
% 0.57/0.76         (~ (l1_pre_topc @ X12)
% 0.57/0.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.57/0.76          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 0.57/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.57/0.76      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.57/0.76  thf('43', plain,
% 0.57/0.76      (((m1_subset_1 @ 
% 0.57/0.76         (k2_pre_topc @ sk_A @ 
% 0.57/0.76          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.57/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.57/0.76  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('45', plain,
% 0.57/0.76      ((m1_subset_1 @ 
% 0.57/0.76        (k2_pre_topc @ sk_A @ 
% 0.57/0.76         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))) @ 
% 0.57/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.57/0.76  thf('46', plain,
% 0.57/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('47', plain,
% 0.57/0.76      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.57/0.76          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.57/0.76        | (v2_struct_0 @ sk_A)
% 0.57/0.76        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.57/0.76      inference('demod', [status(thm)],
% 0.57/0.76                ['25', '26', '27', '28', '40', '45', '46'])).
% 0.57/0.76  thf('48', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.57/0.76      inference('simplify', [status(thm)], ['47'])).
% 0.57/0.76  thf('49', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.57/0.76      inference('clc', [status(thm)], ['48', '49'])).
% 0.57/0.76  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.64/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
