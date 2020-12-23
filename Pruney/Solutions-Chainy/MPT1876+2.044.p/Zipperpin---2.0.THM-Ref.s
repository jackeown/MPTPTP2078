%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qfdBCAlX9B

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:02 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 873 expanded)
%              Number of leaves         :   38 ( 265 expanded)
%              Depth                    :   26
%              Number of atoms          :  934 (8870 expanded)
%              Number of equality atoms :   15 (  64 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('32',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','42'])).

thf('44',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( X26
        = ( u1_struct_0 @ ( sk_C_1 @ X26 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','45','54'])).

thf('56',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51','52','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('63',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( m1_pre_topc @ ( sk_C_1 @ X26 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['94','106'])).

thf('108',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('109',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('113',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('114',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['63','107','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['47','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qfdBCAlX9B
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 171 iterations in 0.105s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.56  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.38/0.56  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(t44_tex_2, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.56         ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.38/0.56  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf(t63_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.38/0.56          | ~ (r2_hidden @ X8 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0)
% 0.38/0.56          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf(t3_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf(t1_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.38/0.56           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X24)
% 0.38/0.56          | ~ (v1_zfmisc_1 @ X24)
% 0.38/0.56          | ((X25) = (X24))
% 0.38/0.56          | ~ (r1_tarski @ X25 @ X24)
% 0.38/0.56          | (v1_xboole_0 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.38/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.56          | ~ (v1_zfmisc_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_zfmisc_1 @ X0)
% 0.38/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.56          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.38/0.56          | (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.38/0.56  thf('13', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X0)
% 0.38/0.56          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.56          | ~ (v1_zfmisc_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i]:
% 0.38/0.56         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.56  thf('18', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf(d3_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X3 @ X4)
% 0.38/0.56          | (r2_hidden @ X3 @ X5)
% 0.38/0.56          | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '20'])).
% 0.38/0.56  thf('22', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf(t1_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.56  thf('25', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf(t36_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X28 : $i, X29 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.38/0.56          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.38/0.56          | ~ (l1_pre_topc @ X29)
% 0.38/0.56          | ~ (v2_pre_topc @ X29)
% 0.38/0.56          | (v2_struct_0 @ X29))),
% 0.38/0.56      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.38/0.56           sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('30', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X19)
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ X19)
% 0.38/0.56          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.38/0.56          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.38/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('35', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.38/0.56         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.38/0.56      inference('clc', [status(thm)], ['32', '35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28', '29', '36'])).
% 0.38/0.56  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('39', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['14', '39'])).
% 0.38/0.56  thf('41', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('42', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('45', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 0.38/0.56  thf('47', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t34_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.56                ( ![C:$i]:
% 0.38/0.56                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.38/0.56                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.56          | ~ (v2_tex_2 @ X26 @ X27)
% 0.38/0.56          | ((X26) = (u1_struct_0 @ (sk_C_1 @ X26 @ X27)))
% 0.38/0.56          | ~ (l1_pre_topc @ X27)
% 0.38/0.56          | ~ (v2_pre_topc @ X27)
% 0.38/0.56          | (v2_struct_0 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.56  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf('54', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.56      inference('split', [status(esa)], ['3'])).
% 0.38/0.56  thf('55', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['2', '45', '54'])).
% 0.38/0.56  thf('56', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '51', '52', '56'])).
% 0.38/0.56  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.38/0.56      inference('clc', [status(thm)], ['57', '58'])).
% 0.38/0.56  thf('60', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('61', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf(fc7_struct_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.56       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X18 : $i]:
% 0.38/0.56         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.38/0.56          | ~ (l1_struct_0 @ X18)
% 0.38/0.56          | ~ (v7_struct_0 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      (((v1_zfmisc_1 @ sk_B_1)
% 0.38/0.56        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['61', '62'])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.56          | ~ (v2_tex_2 @ X26 @ X27)
% 0.38/0.56          | (m1_pre_topc @ (sk_C_1 @ X26 @ X27) @ X27)
% 0.38/0.56          | ~ (l1_pre_topc @ X27)
% 0.38/0.56          | ~ (v2_pre_topc @ X27)
% 0.38/0.56          | (v2_struct_0 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.56  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('69', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.38/0.56  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['70', '71'])).
% 0.38/0.56  thf('73', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('74', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.38/0.56  thf(cc32_tex_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.56         ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.56           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.38/0.56             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (![X22 : $i, X23 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X22 @ X23)
% 0.38/0.56          | ~ (v1_tdlat_3 @ X22)
% 0.38/0.56          | (v7_struct_0 @ X22)
% 0.38/0.56          | (v2_struct_0 @ X22)
% 0.38/0.56          | ~ (l1_pre_topc @ X23)
% 0.38/0.56          | ~ (v2_tdlat_3 @ X23)
% 0.38/0.56          | ~ (v2_pre_topc @ X23)
% 0.38/0.56          | (v2_struct_0 @ X23))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (v2_tdlat_3 @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.56  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('78', plain, ((v2_tdlat_3 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.56          | ~ (v2_tex_2 @ X26 @ X27)
% 0.38/0.56          | (v1_tdlat_3 @ (sk_C_1 @ X26 @ X27))
% 0.38/0.56          | ~ (l1_pre_topc @ X27)
% 0.38/0.56          | ~ (v2_pre_topc @ X27)
% 0.38/0.56          | (v2_struct_0 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.38/0.56  thf('86', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.56  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['87', '88'])).
% 0.38/0.56  thf('90', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('91', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['89', '90'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['76', '77', '78', '79', '91'])).
% 0.38/0.56  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['92', '93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X26)
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.38/0.56          | ~ (v2_tex_2 @ X26 @ X27)
% 0.38/0.56          | ~ (v2_struct_0 @ (sk_C_1 @ X26 @ X27))
% 0.38/0.56          | ~ (l1_pre_topc @ X27)
% 0.38/0.56          | ~ (v2_pre_topc @ X27)
% 0.38/0.56          | (v2_struct_0 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.38/0.56  thf('101', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['53', '55'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.38/0.56  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['102', '103'])).
% 0.38/0.56  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('106', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['104', '105'])).
% 0.38/0.56  thf('107', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['94', '106'])).
% 0.38/0.56  thf('108', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['72', '73'])).
% 0.38/0.56  thf(dt_m1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.56  thf('109', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.38/0.56          | (l1_pre_topc @ X16)
% 0.38/0.56          | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('110', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['108', '109'])).
% 0.38/0.56  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('112', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['110', '111'])).
% 0.38/0.56  thf(dt_l1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('113', plain,
% 0.38/0.56      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('114', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['112', '113'])).
% 0.38/0.56  thf('115', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['63', '107', '114'])).
% 0.38/0.56  thf('116', plain, ($false), inference('demod', [status(thm)], ['47', '115'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
