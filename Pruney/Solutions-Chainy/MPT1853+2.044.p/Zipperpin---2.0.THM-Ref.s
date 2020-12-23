%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GDLZnIcTu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:08 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 947 expanded)
%              Number of leaves         :   40 ( 273 expanded)
%              Depth                    :   24
%              Number of atoms          : 1989 (11586 expanded)
%              Number of equality atoms :   46 ( 190 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('29',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

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

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_tex_2 @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ( v1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_tex_2 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('47',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
        | ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ X0 ) @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
        | ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ X0 ) @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(cc6_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ( ~ ( v1_xboole_0 @ B )
              & ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v1_xboole_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( v7_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc6_tex_2])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v7_struct_0 @ sk_A )
        | ~ ( l1_struct_0 @ sk_A )
        | ( v1_xboole_0 @ X0 )
        | ~ ( v1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X15: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v7_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('67',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('69',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('71',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25
       != ( k6_domain_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( v1_zfmisc_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('79',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('80',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('83',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('85',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','89'])).

thf('91',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('93',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ X0 )
        | ~ ( v1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','91','92','93'])).

thf('95',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','97'])).

thf('99',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('107',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('111',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('118',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('119',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('120',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('122',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( sk_C_1 @ X27 @ X28 )
        = ( u1_struct_0 @ X27 ) )
      | ( v1_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X27 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ( v1_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('129',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('132',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['120','134'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('136',plain,(
    ! [X16: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( v7_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('137',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
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

thf('139',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('140',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('146',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['137','144','145'])).

thf('147',plain,(
    ! [X15: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v7_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('148',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('150',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('152',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('153',plain,
    ( ( ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('155',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( v1_xboole_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( v7_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc6_tex_2])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','160'])).

thf('162',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['120','134'])).

thf('163',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('164',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('166',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('168',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['161','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('173',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','116','117','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GDLZnIcTu
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 304 iterations in 0.160s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.42/0.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.42/0.61  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.42/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.42/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.61  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.42/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(t20_tex_2, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.61           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.42/0.61             ( v1_subset_1 @
% 0.42/0.61               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.61              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.42/0.61                ( v1_subset_1 @
% 0.42/0.61                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.42/0.61                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61           (u1_struct_0 @ sk_A))
% 0.42/0.61        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (~
% 0.42/0.61       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61         (u1_struct_0 @ sk_A))) | 
% 0.42/0.61       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k6_domain_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.42/0.61       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X19 : $i, X20 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X19)
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.42/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.42/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k6_domain_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ X17)
% 0.42/0.61          | (m1_subset_1 @ (k6_domain_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.42/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['4', '7'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.61        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.61  thf(d7_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X30 : $i, X31 : $i]:
% 0.42/0.61         (((X31) = (X30))
% 0.42/0.61          | (v1_subset_1 @ X31 @ X30)
% 0.42/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.61        | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.42/0.61        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.42/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61           (u1_struct_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61               (u1_struct_0 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['0'])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (((~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.42/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.61         <= (~
% 0.42/0.61             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.61               (u1_struct_0 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.42/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.61         <= (~
% 0.42/0.61             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.62  thf(fc2_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.42/0.62          | ~ (l1_struct_0 @ X14)
% 0.42/0.62          | (v2_struct_0 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v2_struct_0 @ sk_A)
% 0.42/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_l1_pre_topc, axiom,
% 0.42/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.62  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '21'])).
% 0.42/0.62  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.42/0.62         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('split', [status(esa)], ['25'])).
% 0.42/0.62  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k1_tex_2, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.42/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.42/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.42/0.62         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X32)
% 0.42/0.62          | (v2_struct_0 @ X32)
% 0.42/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.42/0.62          | (m1_pre_topc @ (k1_tex_2 @ X32 @ X33) @ X32))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | (v2_struct_0 @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.62  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | (v2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('33', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf(t1_tsep_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.62           ( m1_subset_1 @
% 0.42/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X21 @ X22)
% 0.42/0.62          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.42/0.62          | ~ (l1_pre_topc @ X22))),
% 0.42/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.62  thf(d3_tex_2, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.42/0.62           ( ( v1_tex_2 @ B @ A ) <=>
% 0.42/0.62             ( ![C:$i]:
% 0.42/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.42/0.62                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X27 @ X28)
% 0.42/0.62          | ~ (v1_tex_2 @ X27 @ X28)
% 0.42/0.62          | ((X29) != (u1_struct_0 @ X27))
% 0.42/0.62          | (v1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.42/0.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.42/0.62          | ~ (l1_pre_topc @ X28))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X28)
% 0.42/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.42/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.42/0.62          | (v1_subset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28))
% 0.42/0.62          | ~ (v1_tex_2 @ X27 @ X28)
% 0.42/0.62          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.42/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62           (u1_struct_0 @ sk_A))
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['37', '39'])).
% 0.42/0.62  thf('41', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62           (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62         (k1_tarski @ sk_B_1)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))) & 
% 0.42/0.62             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['24', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('47', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (((m1_subset_1 @ sk_B_1 @ (k1_tarski @ sk_B_1)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['46', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X32)
% 0.42/0.62          | (v2_struct_0 @ X32)
% 0.42/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.42/0.62          | (m1_pre_topc @ (k1_tex_2 @ X32 @ X33) @ X32))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (~ (m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62           | (m1_pre_topc @ (k1_tex_2 @ sk_A @ X0) @ sk_A)
% 0.42/0.62           | (v2_struct_0 @ sk_A)
% 0.42/0.62           | ~ (l1_pre_topc @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.42/0.62  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (~ (m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62           | (m1_pre_topc @ (k1_tex_2 @ sk_A @ X0) @ sk_A)
% 0.42/0.62           | (v2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.42/0.62  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          ((m1_pre_topc @ (k1_tex_2 @ sk_A @ X0) @ sk_A)
% 0.42/0.62           | ~ (m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['53', '54'])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['48', '55'])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X21 @ X22)
% 0.42/0.62          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.42/0.62          | ~ (l1_pre_topc @ X22))),
% 0.42/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.42/0.62         | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62         (k1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf(cc6_tex_2, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.62             ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.42/0.62               ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X23 : $i, X24 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.62          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.42/0.62          | (v1_xboole_0 @ X23)
% 0.42/0.62          | ~ (l1_struct_0 @ X24)
% 0.42/0.62          | ~ (v7_struct_0 @ X24)
% 0.42/0.62          | (v2_struct_0 @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc6_tex_2])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))
% 0.42/0.62           | (v2_struct_0 @ sk_A)
% 0.42/0.62           | ~ (v7_struct_0 @ sk_A)
% 0.42/0.62           | ~ (l1_struct_0 @ sk_A)
% 0.42/0.62           | (v1_xboole_0 @ X0)
% 0.42/0.62           | ~ (v1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf(fc6_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.62       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      (![X15 : $i]:
% 0.42/0.62         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X15))
% 0.42/0.62          | ~ (l1_struct_0 @ X15)
% 0.42/0.62          | (v7_struct_0 @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.42/0.62  thf('67', plain,
% 0.42/0.62      (((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v7_struct_0 @ sk_A)
% 0.42/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.42/0.62  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1)) | (v7_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['67', '68'])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.62  thf(d1_tex_2, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.62       ( ( v1_zfmisc_1 @ A ) <=>
% 0.42/0.62         ( ?[B:$i]:
% 0.42/0.62           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (![X25 : $i, X26 : $i]:
% 0.42/0.62         (((X25) != (k6_domain_1 @ X25 @ X26))
% 0.42/0.62          | ~ (m1_subset_1 @ X26 @ X25)
% 0.42/0.62          | (v1_zfmisc_1 @ X25)
% 0.42/0.62          | (v1_xboole_0 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      ((((u1_struct_0 @ sk_A) != (k1_tarski @ sk_B_1))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.42/0.62  thf('74', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      ((((u1_struct_0 @ sk_A) != (k1_tarski @ sk_B_1))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | ((u1_struct_0 @ sk_A) != (k1_tarski @ sk_B_1)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['75'])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      (((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['70', '76'])).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('79', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      (((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      ((((v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.42/0.62  thf(d1_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.62  thf('83', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['82'])).
% 0.42/0.62  thf(dt_k2_subset_1, axiom,
% 0.42/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.62  thf('85', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.62  thf('86', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.42/0.62      inference('demod', [status(thm)], ['84', '85'])).
% 0.42/0.62  thf(t5_subset, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X8 @ X9)
% 0.42/0.62          | ~ (v1_xboole_0 @ X10)
% 0.42/0.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.62  thf('88', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.42/0.62  thf('89', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['83', '88'])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      (((v1_zfmisc_1 @ (k1_tarski @ sk_B_1)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['81', '89'])).
% 0.42/0.62  thf('91', plain,
% 0.42/0.62      (((v7_struct_0 @ sk_A))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '90'])).
% 0.42/0.62  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('93', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('94', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))
% 0.42/0.62           | (v2_struct_0 @ sk_A)
% 0.42/0.62           | (v1_xboole_0 @ X0)
% 0.42/0.62           | ~ (v1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['64', '91', '92', '93'])).
% 0.42/0.62  thf('95', plain,
% 0.42/0.62      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62            (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.42/0.62         | (v2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['61', '94'])).
% 0.42/0.62  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('97', plain,
% 0.42/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.42/0.62         | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62              (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['95', '96'])).
% 0.42/0.62  thf('98', plain,
% 0.42/0.62      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))) & 
% 0.42/0.62             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['45', '97'])).
% 0.42/0.62  thf('99', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.42/0.62          | ~ (l1_struct_0 @ X14)
% 0.42/0.62          | (v2_struct_0 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.42/0.62  thf('100', plain,
% 0.42/0.62      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.42/0.62         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))) & 
% 0.42/0.62             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.42/0.62  thf('101', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf(dt_m1_pre_topc, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_pre_topc @ A ) =>
% 0.42/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.42/0.62  thf('102', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X12 @ X13)
% 0.42/0.62          | (l1_pre_topc @ X12)
% 0.42/0.62          | ~ (l1_pre_topc @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.42/0.62  thf('103', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['101', '102'])).
% 0.42/0.62  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('105', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('demod', [status(thm)], ['103', '104'])).
% 0.42/0.62  thf('106', plain,
% 0.42/0.62      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.62  thf('107', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.42/0.62  thf('108', plain,
% 0.42/0.62      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))) & 
% 0.42/0.62             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['100', '107'])).
% 0.42/0.62  thf('109', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('110', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X32)
% 0.42/0.62          | (v2_struct_0 @ X32)
% 0.42/0.62          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.42/0.62          | ~ (v2_struct_0 @ (k1_tex_2 @ X32 @ X33)))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.42/0.62  thf('111', plain,
% 0.42/0.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.42/0.62        | (v2_struct_0 @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.42/0.62  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('113', plain,
% 0.42/0.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.42/0.62  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('115', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['113', '114'])).
% 0.42/0.62  thf('116', plain,
% 0.42/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A))) | 
% 0.42/0.62       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['108', '115'])).
% 0.42/0.62  thf('117', plain,
% 0.42/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A))) | 
% 0.42/0.62       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('split', [status(esa)], ['25'])).
% 0.42/0.62  thf('118', plain,
% 0.42/0.62      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.62  thf('119', plain,
% 0.42/0.62      (![X30 : $i, X31 : $i]:
% 0.42/0.62         (((X31) = (X30))
% 0.42/0.62          | (v1_subset_1 @ X31 @ X30)
% 0.42/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.42/0.62  thf('120', plain,
% 0.42/0.62      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A))
% 0.42/0.62        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['118', '119'])).
% 0.42/0.62  thf('121', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('122', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X27 @ X28)
% 0.42/0.62          | ((sk_C_1 @ X27 @ X28) = (u1_struct_0 @ X27))
% 0.42/0.62          | (v1_tex_2 @ X27 @ X28)
% 0.42/0.62          | ~ (l1_pre_topc @ X28))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.42/0.62  thf('123', plain,
% 0.42/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.42/0.62        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['121', '122'])).
% 0.42/0.62  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('125', plain,
% 0.42/0.62      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.42/0.62      inference('demod', [status(thm)], ['123', '124'])).
% 0.42/0.62  thf('126', plain,
% 0.42/0.62      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('127', plain,
% 0.42/0.62      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['125', '126'])).
% 0.42/0.62  thf('128', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i]:
% 0.42/0.62         (~ (m1_pre_topc @ X27 @ X28)
% 0.42/0.62          | ~ (v1_subset_1 @ (sk_C_1 @ X27 @ X28) @ (u1_struct_0 @ X28))
% 0.42/0.62          | (v1_tex_2 @ X27 @ X28)
% 0.42/0.62          | ~ (l1_pre_topc @ X28))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.42/0.62  thf('129', plain,
% 0.42/0.62      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62            (u1_struct_0 @ sk_A))
% 0.42/0.62         | ~ (l1_pre_topc @ sk_A)
% 0.42/0.62         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.42/0.62         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['127', '128'])).
% 0.42/0.62  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('131', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.42/0.62      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('132', plain,
% 0.42/0.62      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62            (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.42/0.62  thf('133', plain,
% 0.42/0.62      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('134', plain,
% 0.42/0.62      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.42/0.62           (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('clc', [status(thm)], ['132', '133'])).
% 0.42/0.62  thf('135', plain,
% 0.42/0.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['120', '134'])).
% 0.42/0.62  thf(fc7_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.62       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.42/0.62  thf('136', plain,
% 0.42/0.62      (![X16 : $i]:
% 0.42/0.62         ((v1_zfmisc_1 @ (u1_struct_0 @ X16))
% 0.42/0.62          | ~ (l1_struct_0 @ X16)
% 0.42/0.62          | ~ (v7_struct_0 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.42/0.62  thf('137', plain,
% 0.42/0.62      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.42/0.62         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['135', '136'])).
% 0.42/0.62  thf('138', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(fc2_tex_2, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.42/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.42/0.62         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.42/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.42/0.62  thf('139', plain,
% 0.42/0.62      (![X34 : $i, X35 : $i]:
% 0.42/0.62         (~ (l1_pre_topc @ X34)
% 0.42/0.62          | (v2_struct_0 @ X34)
% 0.42/0.62          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 0.42/0.62          | (v7_struct_0 @ (k1_tex_2 @ X34 @ X35)))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.42/0.62  thf('140', plain,
% 0.42/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.42/0.62        | (v2_struct_0 @ sk_A)
% 0.42/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['138', '139'])).
% 0.42/0.62  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('142', plain,
% 0.42/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['140', '141'])).
% 0.42/0.62  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('144', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['142', '143'])).
% 0.42/0.62  thf('145', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.42/0.62  thf('146', plain,
% 0.42/0.62      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['137', '144', '145'])).
% 0.42/0.62  thf('147', plain,
% 0.42/0.62      (![X15 : $i]:
% 0.42/0.62         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X15))
% 0.42/0.62          | ~ (l1_struct_0 @ X15)
% 0.42/0.62          | (v7_struct_0 @ X15))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.42/0.62  thf('148', plain,
% 0.42/0.62      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['146', '147'])).
% 0.42/0.62  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('150', plain,
% 0.42/0.62      (((v7_struct_0 @ sk_A))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['148', '149'])).
% 0.42/0.62  thf('151', plain,
% 0.42/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.42/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.62  thf('152', plain,
% 0.42/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('split', [status(esa)], ['25'])).
% 0.42/0.62  thf('153', plain,
% 0.42/0.62      ((((v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['151', '152'])).
% 0.42/0.62  thf('154', plain,
% 0.42/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.42/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.62  thf('155', plain,
% 0.42/0.62      (![X23 : $i, X24 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.42/0.62          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.42/0.62          | (v1_xboole_0 @ X23)
% 0.42/0.62          | ~ (l1_struct_0 @ X24)
% 0.42/0.62          | ~ (v7_struct_0 @ X24)
% 0.42/0.62          | (v2_struct_0 @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc6_tex_2])).
% 0.42/0.62  thf('156', plain,
% 0.42/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v2_struct_0 @ sk_A)
% 0.42/0.62        | ~ (v7_struct_0 @ sk_A)
% 0.42/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.42/0.62        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62        | ~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['154', '155'])).
% 0.42/0.62  thf('157', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('158', plain,
% 0.42/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | (v2_struct_0 @ sk_A)
% 0.42/0.62        | ~ (v7_struct_0 @ sk_A)
% 0.42/0.62        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62        | ~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['156', '157'])).
% 0.42/0.62  thf('159', plain,
% 0.42/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | ~ (v7_struct_0 @ sk_A)
% 0.42/0.62         | (v2_struct_0 @ sk_A)
% 0.42/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['153', '158'])).
% 0.42/0.62  thf('160', plain,
% 0.42/0.62      ((((v2_struct_0 @ sk_A)
% 0.42/0.62         | ~ (v7_struct_0 @ sk_A)
% 0.42/0.62         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.42/0.62         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['159'])).
% 0.42/0.62  thf('161', plain,
% 0.42/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.42/0.62         | (v2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['150', '160'])).
% 0.42/0.62  thf('162', plain,
% 0.42/0.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['120', '134'])).
% 0.42/0.62  thf('163', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.42/0.62          | ~ (l1_struct_0 @ X14)
% 0.42/0.62          | (v2_struct_0 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.42/0.62  thf('164', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.42/0.62         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['162', '163'])).
% 0.42/0.62  thf('165', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.42/0.62  thf('166', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.62         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['164', '165'])).
% 0.42/0.62  thf('167', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.42/0.62      inference('clc', [status(thm)], ['113', '114'])).
% 0.42/0.62  thf('168', plain,
% 0.42/0.62      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.42/0.62      inference('clc', [status(thm)], ['166', '167'])).
% 0.42/0.62  thf('169', plain,
% 0.42/0.62      ((((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B_1))))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['161', '168'])).
% 0.42/0.62  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('171', plain,
% 0.42/0.62      (((v1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.42/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.42/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62               (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['169', '170'])).
% 0.42/0.62  thf('172', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['83', '88'])).
% 0.42/0.62  thf('173', plain,
% 0.42/0.62      (~
% 0.42/0.62       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.42/0.62         (u1_struct_0 @ sk_A))) | 
% 0.42/0.62       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['171', '172'])).
% 0.42/0.62  thf('174', plain, ($false),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['1', '116', '117', '173'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
