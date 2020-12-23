%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dLWwNEA58C

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  166 (1144 expanded)
%              Number of leaves         :   40 ( 333 expanded)
%              Depth                    :   25
%              Number of atoms          : 1007 (12626 expanded)
%              Number of equality atoms :   15 (  94 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ~ ( v2_struct_0 @ ( sk_C @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','46'])).

thf('48',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','49','50'])).

thf('52',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( m1_pre_topc @ ( sk_C @ X27 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','51'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(cc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('73',plain,(
    ! [X22: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ~ ( v2_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('74',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( v1_tdlat_3 @ ( sk_C @ X27 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','51'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('87',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_tdlat_3 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(cc2_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('97',plain,(
    ! [X21: $i] :
      ( ~ ( v2_tdlat_3 @ X21 )
      | ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_tdlat_3])).

thf('98',plain,
    ( ( v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('100',plain,(
    v2_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','95','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tex_2 @ X27 @ X28 )
      | ( X27
        = ( u1_struct_0 @ ( sk_C @ X27 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','51'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('113',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('114',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('116',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','49'])).

thf('117',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','117'])).

thf('119',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('120',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('121',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['101','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['57','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dLWwNEA58C
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 100 iterations in 0.063s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.36/0.55  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.36/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(t44_tex_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.36/0.55         ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t34_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.36/0.55                ( ![C:$i]:
% 0.36/0.55                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.36/0.55                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.55                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X27)
% 0.36/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.55          | ~ (v2_tex_2 @ X27 @ X28)
% 0.36/0.55          | ~ (v2_struct_0 @ (sk_C @ X27 @ X28))
% 0.36/0.55          | ~ (l1_pre_topc @ X28)
% 0.36/0.55          | ~ (v2_pre_topc @ X28)
% 0.36/0.55          | (v2_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.55  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('split', [status(esa)], ['6'])).
% 0.36/0.55  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['6'])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf(t63_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.36/0.55          | ~ (r2_hidden @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0)
% 0.36/0.55          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]:
% 0.36/0.55         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf(t1_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.36/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X25)
% 0.36/0.55          | ~ (v1_zfmisc_1 @ X25)
% 0.36/0.55          | ((X26) = (X25))
% 0.36/0.55          | ~ (r1_tarski @ X26 @ X25)
% 0.36/0.55          | (v1_xboole_0 @ X26))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0)
% 0.36/0.55          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.36/0.55          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.36/0.55          | (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_zfmisc_1 @ X0)
% 0.36/0.55          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.55          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.36/0.55          | (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.55  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.36/0.55  thf('19', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0)
% 0.36/0.55          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.36/0.55          | ~ (v1_zfmisc_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t4_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X11 @ X12)
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.36/0.55          | (m1_subset_1 @ X11 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.55        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '24'])).
% 0.36/0.55  thf('26', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf(t36_tex_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X29 : $i, X30 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.36/0.55          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 0.36/0.55          | ~ (l1_pre_topc @ X30)
% 0.36/0.55          | ~ (v2_pre_topc @ X30)
% 0.36/0.55          | (v2_struct_0 @ X30))),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.36/0.55           sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.55  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('32', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X19)
% 0.36/0.55          | ~ (m1_subset_1 @ X20 @ X19)
% 0.36/0.55          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.36/0.55          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_subset_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.36/0.55          | (v1_xboole_0 @ X6)
% 0.36/0.55          | ~ (v1_xboole_0 @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('39', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.36/0.55         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.36/0.55      inference('clc', [status(thm)], ['34', '39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['29', '30', '31', '40'])).
% 0.36/0.55  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('43', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['20', '43'])).
% 0.36/0.55  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('46', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '46'])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('49', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.55  thf('50', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.55      inference('split', [status(esa)], ['6'])).
% 0.36/0.55  thf('51', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['9', '49', '50'])).
% 0.36/0.55  thf('52', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['7', '51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['5', '52'])).
% 0.36/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.36/0.55  thf('56', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('57', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['55', '56'])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X27)
% 0.36/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.55          | ~ (v2_tex_2 @ X27 @ X28)
% 0.36/0.55          | (m1_pre_topc @ (sk_C @ X27 @ X28) @ X28)
% 0.36/0.55          | ~ (l1_pre_topc @ X28)
% 0.36/0.55          | ~ (v2_pre_topc @ X28)
% 0.36/0.55          | (v2_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.55  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('63', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['7', '51'])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.36/0.55  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['64', '65'])).
% 0.36/0.55  thf('67', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('68', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['66', '67'])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.36/0.55          | (l1_pre_topc @ X16)
% 0.36/0.55          | ~ (l1_pre_topc @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.55  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('72', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.55  thf(cc2_tex_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.36/0.55         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      (![X22 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X22)
% 0.36/0.55          | ~ (v2_pre_topc @ X22)
% 0.36/0.55          | ~ (v1_tdlat_3 @ X22)
% 0.36/0.55          | ~ (v2_tdlat_3 @ X22)
% 0.36/0.55          | (v7_struct_0 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X27)
% 0.36/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.55          | ~ (v2_tex_2 @ X27 @ X28)
% 0.36/0.55          | (v1_tdlat_3 @ (sk_C @ X27 @ X28))
% 0.36/0.55          | ~ (l1_pre_topc @ X28)
% 0.36/0.55          | ~ (v2_pre_topc @ X28)
% 0.36/0.55          | (v2_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.55  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('80', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['7', '51'])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.36/0.55  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('83', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['81', '82'])).
% 0.36/0.55  thf('84', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('85', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['83', '84'])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['74', '85'])).
% 0.36/0.55  thf('87', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.36/0.55      inference('clc', [status(thm)], ['66', '67'])).
% 0.36/0.55  thf(cc6_tdlat_3, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.36/0.55         ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X23 @ X24)
% 0.36/0.55          | (v2_tdlat_3 @ X23)
% 0.36/0.55          | ~ (l1_pre_topc @ X24)
% 0.36/0.55          | ~ (v2_tdlat_3 @ X24)
% 0.36/0.55          | ~ (v2_pre_topc @ X24)
% 0.36/0.55          | (v2_struct_0 @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (v2_tdlat_3 @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.36/0.55  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('91', plain, ((v2_tdlat_3 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('93', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.36/0.55  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('95', plain, ((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.36/0.55  thf('96', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.55  thf(cc2_tdlat_3, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) => ( ( v2_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.36/0.55  thf('97', plain,
% 0.36/0.55      (![X21 : $i]:
% 0.36/0.55         (~ (v2_tdlat_3 @ X21) | (v2_pre_topc @ X21) | ~ (l1_pre_topc @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_tdlat_3])).
% 0.36/0.55  thf('98', plain,
% 0.36/0.55      (((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.55  thf('99', plain, ((v2_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.36/0.55  thf('100', plain, ((v2_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.36/0.55  thf('101', plain,
% 0.36/0.55      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['86', '95', '100'])).
% 0.36/0.55  thf('102', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('103', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X27)
% 0.36/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.55          | ~ (v2_tex_2 @ X27 @ X28)
% 0.36/0.55          | ((X27) = (u1_struct_0 @ (sk_C @ X27 @ X28)))
% 0.36/0.55          | ~ (l1_pre_topc @ X28)
% 0.36/0.55          | ~ (v2_pre_topc @ X28)
% 0.36/0.55          | (v2_struct_0 @ X28))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.36/0.55  thf('104', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.36/0.55        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['102', '103'])).
% 0.36/0.55  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('107', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['7', '51'])).
% 0.36/0.55  thf('108', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.36/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.55      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.36/0.55  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('110', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.55        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.36/0.55      inference('clc', [status(thm)], ['108', '109'])).
% 0.36/0.55  thf('111', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('112', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['110', '111'])).
% 0.36/0.55  thf(fc7_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf('113', plain,
% 0.36/0.55      (![X18 : $i]:
% 0.36/0.55         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.36/0.55          | ~ (l1_struct_0 @ X18)
% 0.36/0.55          | ~ (v7_struct_0 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.36/0.55  thf('114', plain,
% 0.36/0.55      (((v1_zfmisc_1 @ sk_B_1)
% 0.36/0.55        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['112', '113'])).
% 0.36/0.55  thf('115', plain,
% 0.36/0.55      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.36/0.55      inference('split', [status(esa)], ['8'])).
% 0.36/0.55  thf('116', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['9', '49'])).
% 0.36/0.55  thf('117', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 0.36/0.55  thf('118', plain,
% 0.36/0.55      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.36/0.55        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.36/0.55      inference('clc', [status(thm)], ['114', '117'])).
% 0.36/0.55  thf('119', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('120', plain,
% 0.36/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('121', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['119', '120'])).
% 0.36/0.55  thf('122', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['118', '121'])).
% 0.36/0.55  thf('123', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['101', '122'])).
% 0.36/0.55  thf('124', plain, ($false), inference('demod', [status(thm)], ['57', '123'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
