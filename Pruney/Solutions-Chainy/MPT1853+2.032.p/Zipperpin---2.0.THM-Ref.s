%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGZtqOrjJj

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  159 (1133 expanded)
%              Number of leaves         :   35 ( 321 expanded)
%              Depth                    :   29
%              Number of atoms          : 1355 (14867 expanded)
%              Number of equality atoms :   28 ( 112 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X21 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('16',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('26',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( sk_C @ X16 @ X17 )
        = ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('33',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v1_subset_1 @ ( sk_C @ X16 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ( v1_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('35',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('38',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('40',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v7_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('54',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','51','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('63',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['60','67'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','71'])).

thf('73',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['10','72'])).

thf('74',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('75',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v1_tex_2 @ X16 @ X17 )
      | ( X18
       != ( u1_struct_0 @ X16 ) )
      | ( v1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tex_2 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('84',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['11','71','83'])).

thf('85',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('91',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( X28 = X27 )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('94',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
       != ( k6_domain_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( v1_zfmisc_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('95',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('100',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','71'])).

thf('102',plain,(
    v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','102'])).

thf('104',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('105',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['103','106'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('108',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('109',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('113',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','113'])).

thf('115',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['117','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGZtqOrjJj
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 177 iterations in 0.100s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.22/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.56  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.56  thf(t20_tex_2, conjecture,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.56           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.56             ( v1_subset_1 @
% 0.22/0.56               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i]:
% 0.22/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56          ( ![B:$i]:
% 0.22/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.56              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.56                ( v1_subset_1 @
% 0.22/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.56                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.22/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k6_domain_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ X8)
% 0.22/0.56          | ~ (m1_subset_1 @ X9 @ X8)
% 0.22/0.56          | (m1_subset_1 @ (k6_domain_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.56  thf(d7_subset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.56       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i]:
% 0.22/0.56         (((X20) = (X19))
% 0.22/0.56          | (v1_subset_1 @ X20 @ X19)
% 0.22/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A))
% 0.22/0.56        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (((~ (v1_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (~
% 0.22/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A))) | 
% 0.22/0.56       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('split', [status(esa)], ['12'])).
% 0.22/0.56  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k1_tex_2, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.56         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X21 : $i, X22 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X21)
% 0.22/0.56          | (v2_struct_0 @ X21)
% 0.22/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.22/0.56          | (m1_pre_topc @ (k1_tex_2 @ X21 @ X22) @ X21))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.56  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('20', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(t1_tsep_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.56           ( m1_subset_1 @
% 0.22/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.56          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.22/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.56          | ~ (l1_pre_topc @ X11))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i]:
% 0.22/0.56         (((X20) = (X19))
% 0.22/0.56          | (v1_subset_1 @ X20 @ X19)
% 0.22/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A))
% 0.22/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.56  thf('27', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(d3_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.56           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.56             ( ![C:$i]:
% 0.22/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.56                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.56          | ((sk_C @ X16 @ X17) = (u1_struct_0 @ X16))
% 0.22/0.56          | (v1_tex_2 @ X16 @ X17)
% 0.22/0.56          | ~ (l1_pre_topc @ X17))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.56  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.56          | ~ (v1_subset_1 @ (sk_C @ X16 @ X17) @ (u1_struct_0 @ X17))
% 0.22/0.56          | (v1_tex_2 @ X16 @ X17)
% 0.22/0.56          | ~ (l1_pre_topc @ X17))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56            (u1_struct_0 @ sk_A))
% 0.22/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('37', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56            (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['26', '40'])).
% 0.22/0.56  thf(t8_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.56           ( ~( ( v1_subset_1 @
% 0.22/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.56                  ( u1_struct_0 @ A ) ) & 
% 0.22/0.56                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (![X29 : $i, X30 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.22/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ 
% 0.22/0.56               (u1_struct_0 @ X30))
% 0.22/0.56          | ~ (v7_struct_0 @ X30)
% 0.22/0.56          | ~ (l1_struct_0 @ X30)
% 0.22/0.56          | (v2_struct_0 @ X30))),
% 0.22/0.56      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (~ (v1_subset_1 @ 
% 0.22/0.56              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0) @ 
% 0.22/0.56              (u1_struct_0 @ sk_A))
% 0.22/0.56           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['26', '40'])).
% 0.22/0.56  thf('45', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(dt_m1_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      (![X4 : $i, X5 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.56  thf('47', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('49', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.56  thf(dt_l1_pre_topc, axiom,
% 0.22/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.56  thf('50', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.56  thf('51', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.56  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(fc2_tex_2, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.56         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      (![X23 : $i, X24 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X23)
% 0.22/0.56          | (v2_struct_0 @ X23)
% 0.22/0.56          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.22/0.56          | (v7_struct_0 @ (k1_tex_2 @ X23 @ X24)))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.56  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('58', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.56  thf('59', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['26', '40'])).
% 0.22/0.56  thf('60', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.22/0.56              (u1_struct_0 @ sk_A))
% 0.22/0.56           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['43', '44', '51', '58', '59'])).
% 0.22/0.56  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('62', plain,
% 0.22/0.56      (![X21 : $i, X22 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X21)
% 0.22/0.56          | (v2_struct_0 @ X21)
% 0.22/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.22/0.56          | ~ (v2_struct_0 @ (k1_tex_2 @ X21 @ X22)))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.56  thf('63', plain,
% 0.22/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('65', plain,
% 0.22/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.56  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('67', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.56  thf('68', plain,
% 0.22/0.56      ((![X0 : $i]:
% 0.22/0.56          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.22/0.56                (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('clc', [status(thm)], ['60', '67'])).
% 0.22/0.56  thf('69', plain,
% 0.22/0.56      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['13', '68'])).
% 0.22/0.56  thf('70', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('71', plain,
% 0.22/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.22/0.56       ~
% 0.22/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.56  thf('72', plain,
% 0.22/0.56      (~
% 0.22/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['11', '71'])).
% 0.22/0.56  thf('73', plain,
% 0.22/0.56      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['10', '72'])).
% 0.22/0.56  thf('74', plain,
% 0.22/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.22/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['12'])).
% 0.22/0.56  thf('75', plain,
% 0.22/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('76', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.56          | ~ (v1_tex_2 @ X16 @ X17)
% 0.22/0.56          | ((X18) != (u1_struct_0 @ X16))
% 0.22/0.56          | (v1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.22/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.56          | ~ (l1_pre_topc @ X17))),
% 0.22/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.56  thf('77', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i]:
% 0.22/0.56         (~ (l1_pre_topc @ X17)
% 0.22/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.22/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.56          | (v1_subset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))
% 0.22/0.56          | ~ (v1_tex_2 @ X16 @ X17)
% 0.22/0.56          | ~ (m1_pre_topc @ X16 @ X17))),
% 0.22/0.56      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.56  thf('78', plain,
% 0.22/0.56      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['75', '77'])).
% 0.22/0.56  thf('79', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('81', plain,
% 0.22/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.22/0.56        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.22/0.56  thf('82', plain,
% 0.22/0.56      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['74', '81'])).
% 0.22/0.56  thf('83', plain,
% 0.22/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.22/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['12'])).
% 0.22/0.56  thf('84', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['11', '71', '83'])).
% 0.22/0.56  thf('85', plain,
% 0.22/0.56      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56        (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.22/0.56  thf('86', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.56      inference('clc', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(t35_borsuk_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.56           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.56  thf('87', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.56          | (r1_tarski @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13))
% 0.22/0.56          | ~ (l1_pre_topc @ X13))),
% 0.22/0.56      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.22/0.56  thf('88', plain,
% 0.22/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56           (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.56  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('90', plain,
% 0.22/0.56      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56        (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.22/0.56  thf(t1_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.56           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.56  thf('91', plain,
% 0.22/0.56      (![X27 : $i, X28 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ X27)
% 0.22/0.56          | ~ (v1_zfmisc_1 @ X27)
% 0.22/0.56          | ((X28) = (X27))
% 0.22/0.56          | ~ (r1_tarski @ X28 @ X27)
% 0.22/0.56          | (v1_xboole_0 @ X28))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.56  thf('92', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.22/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.22/0.56  thf('93', plain,
% 0.22/0.56      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.56  thf(d1_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.56       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.56         ( ?[B:$i]:
% 0.22/0.56           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('94', plain,
% 0.22/0.56      (![X14 : $i, X15 : $i]:
% 0.22/0.56         (((X14) != (k6_domain_1 @ X14 @ X15))
% 0.22/0.56          | ~ (m1_subset_1 @ X15 @ X14)
% 0.22/0.56          | (v1_zfmisc_1 @ X14)
% 0.22/0.56          | (v1_xboole_0 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.56  thf('95', plain,
% 0.22/0.56      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.56  thf('96', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('97', plain,
% 0.22/0.56      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.56  thf('98', plain,
% 0.22/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['97'])).
% 0.22/0.56  thf(cc1_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.22/0.56  thf('99', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.22/0.56  thf('100', plain,
% 0.22/0.56      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56               (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('clc', [status(thm)], ['98', '99'])).
% 0.22/0.56  thf('101', plain,
% 0.22/0.56      (~
% 0.22/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.56         (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['11', '71'])).
% 0.22/0.56  thf('102', plain, ((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['100', '101'])).
% 0.22/0.56  thf('103', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.22/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['92', '102'])).
% 0.22/0.56  thf('104', plain,
% 0.22/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.22/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf(cc1_subset_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.56  thf('105', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.22/0.56          | (v1_xboole_0 @ X1)
% 0.22/0.56          | ~ (v1_xboole_0 @ X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.56  thf('106', plain,
% 0.22/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.56  thf('107', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.22/0.56      inference('clc', [status(thm)], ['103', '106'])).
% 0.22/0.56  thf(fc2_struct_0, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.56  thf('108', plain,
% 0.22/0.56      (![X7 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.22/0.56          | ~ (l1_struct_0 @ X7)
% 0.22/0.56          | (v2_struct_0 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.56  thf('109', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.22/0.56        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.56  thf('110', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.56  thf('111', plain,
% 0.22/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.22/0.56      inference('demod', [status(thm)], ['109', '110'])).
% 0.22/0.56  thf('112', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.22/0.56      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.56  thf('113', plain,
% 0.22/0.56      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('clc', [status(thm)], ['111', '112'])).
% 0.22/0.56  thf('114', plain,
% 0.22/0.56      ((v1_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['85', '113'])).
% 0.22/0.56  thf('115', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['73', '114'])).
% 0.22/0.56  thf('116', plain,
% 0.22/0.56      (![X7 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.22/0.56          | ~ (l1_struct_0 @ X7)
% 0.22/0.56          | (v2_struct_0 @ X7))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.56  thf('117', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['115', '116'])).
% 0.22/0.56  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('119', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.56  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.56      inference('sup-', [status(thm)], ['118', '119'])).
% 0.22/0.56  thf('121', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('demod', [status(thm)], ['117', '120'])).
% 0.22/0.56  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.42/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
