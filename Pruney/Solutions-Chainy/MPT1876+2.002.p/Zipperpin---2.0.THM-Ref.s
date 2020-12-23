%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C2rPNF1gsr

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 479 expanded)
%              Number of leaves         :   31 ( 146 expanded)
%              Depth                    :   17
%              Number of atoms          : 1030 (5442 expanded)
%              Number of equality atoms :   13 (  44 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X11 @ X10 ) )
        = X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v2_tex_2 @ X20 @ X19 )
      | ( v1_tdlat_3 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_tdlat_3 @ X18 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B @ X0 )
      | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X2 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','21'])).

thf('23',plain,
    ( ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

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

thf('41',plain,(
    ! [X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( v2_tdlat_3 @ X15 )
      | ( v7_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('42',plain,
    ( ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','48'])).

thf('50',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v2_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('61',plain,
    ( ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X9: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( v7_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('65',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
   <= ~ ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('73',plain,
    ( ( v1_zfmisc_1 @ sk_B )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X8: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v7_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('76',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('78',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(cc1_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v7_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v1_tdlat_3 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_1])).

thf('82',plain,
    ( ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('84',plain,
    ( ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('86',plain,
    ( ~ ( v7_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('89',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tdlat_3 @ X18 )
      | ( v2_tex_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('90',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tdlat_3 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_tex_2 @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v2_tex_2 @ sk_B @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','70','71','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C2rPNF1gsr
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 74 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.49  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(t44_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.49         ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.21/0.49  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B) | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain, (((v1_zfmisc_1 @ sk_B) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t29_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ((u1_struct_0 @ (k1_pre_topc @ X11 @ X10)) = (X10))
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(t26_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X18)
% 0.21/0.49          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.49          | ((X20) != (u1_struct_0 @ X18))
% 0.21/0.49          | ~ (v2_tex_2 @ X20 @ X19)
% 0.21/0.49          | (v1_tdlat_3 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.49          | ~ (l1_pre_topc @ X19)
% 0.21/0.49          | (v2_struct_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_pre_topc @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.49          | (v1_tdlat_3 @ X18)
% 0.21/0.49          | ~ (v2_tex_2 @ (u1_struct_0 @ X18) @ X19)
% 0.21/0.49          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.49          | (v2_struct_0 @ X18))),
% 0.21/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0)
% 0.21/0.49          | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.49  thf('13', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.49          | ~ (v2_tex_2 @ sk_B @ X0)
% 0.21/0.49          | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.49        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '14'])).
% 0.21/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k1_pre_topc, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.21/0.49         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.49          | (m1_pre_topc @ (k1_pre_topc @ X2 @ X3) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49         | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.49         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '22'])).
% 0.21/0.49  thf('24', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf(fc1_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.21/0.49          | ~ (l1_struct_0 @ X7)
% 0.21/0.49          | ~ (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((v1_xboole_0 @ sk_B)
% 0.21/0.50        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('34', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('35', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.50         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['23', '36'])).
% 0.21/0.50  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.50         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(cc2_tex_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.21/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X15 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X15)
% 0.21/0.50          | ~ (v2_pre_topc @ X15)
% 0.21/0.50          | ~ (v1_tdlat_3 @ X15)
% 0.21/0.50          | ~ (v2_tdlat_3 @ X15)
% 0.21/0.50          | (v7_struct_0 @ X15)
% 0.21/0.50          | ~ (l1_pre_topc @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (((v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v2_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v2_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(cc1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.50          | (v2_pre_topc @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X1)
% 0.21/0.50          | ~ (v2_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((v2_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v2_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '48'])).
% 0.21/0.50  thf('50', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf(cc6_tdlat_3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.21/0.50         ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.50          | (v2_tdlat_3 @ X16)
% 0.21/0.50          | ~ (l1_pre_topc @ X17)
% 0.21/0.50          | ~ (v2_tdlat_3 @ X17)
% 0.21/0.50          | ~ (v2_pre_topc @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50        | ~ (v2_tdlat_3 @ sk_A)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | (v2_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain, ((v2_tdlat_3 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.21/0.50  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain, ((v2_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '58'])).
% 0.21/0.50  thf('60', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '35'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (((v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.50         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '61'])).
% 0.21/0.50  thf('63', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf(fc7_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X9 : $i]:
% 0.21/0.50         ((v1_zfmisc_1 @ (u1_struct_0 @ X9))
% 0.21/0.50          | ~ (l1_struct_0 @ X9)
% 0.21/0.50          | ~ (v7_struct_0 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (((v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | ~ (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['63', '64'])).
% 0.21/0.50  thf('66', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (((v1_zfmisc_1 @ sk_B) | ~ (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '67'])).
% 0.21/0.50  thf('69', plain, ((~ (v1_zfmisc_1 @ sk_B)) <= (~ ((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('70', plain, (((v1_zfmisc_1 @ sk_B)) | ~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, (((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('72', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('73', plain, (((v1_zfmisc_1 @ sk_B)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('74', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf(fc6_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      (![X8 : $i]:
% 0.21/0.50         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X8))
% 0.21/0.50          | ~ (l1_struct_0 @ X8)
% 0.21/0.50          | (v7_struct_0 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((~ (v1_zfmisc_1 @ sk_B)
% 0.21/0.50        | (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      ((~ (v1_zfmisc_1 @ sk_B) | (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (((v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['73', '78'])).
% 0.21/0.50  thf('80', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf(cc1_tex_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.21/0.50         ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) ) ))).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      (![X13 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X13)
% 0.21/0.50          | ~ (v7_struct_0 @ X13)
% 0.21/0.50          | ~ (v2_pre_topc @ X13)
% 0.21/0.50          | (v1_tdlat_3 @ X13)
% 0.21/0.50          | ~ (l1_pre_topc @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_tex_1])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v2_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.50  thf('83', plain, ((v2_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.50  thf('85', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '35'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      ((~ (v7_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['79', '86'])).
% 0.21/0.50  thf('88', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.50          | ((X20) != (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (v1_tdlat_3 @ X18)
% 0.21/0.50          | (v2_tex_2 @ X20 @ X19)
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.50          | ~ (l1_pre_topc @ X19)
% 0.21/0.50          | (v2_struct_0 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X19)
% 0.21/0.50          | ~ (l1_pre_topc @ X19)
% 0.21/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.50          | (v2_tex_2 @ (u1_struct_0 @ X18) @ X19)
% 0.21/0.50          | ~ (v1_tdlat_3 @ X18)
% 0.21/0.50          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.50          | (v2_struct_0 @ X18))),
% 0.21/0.50      inference('simplify', [status(thm)], ['89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50          | (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '90'])).
% 0.21/0.50  thf('92', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50          | (v2_tex_2 @ sk_B @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_struct_0 @ X0)
% 0.21/0.50           | ~ (l1_pre_topc @ X0)
% 0.21/0.50           | (v2_tex_2 @ sk_B @ X0)
% 0.21/0.50           | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.50           | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '93'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50         | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50         | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '94'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      ((((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.50         | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.50         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.21/0.50  thf('99', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '35'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B @ sk_A)))
% 0.21/0.50         <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['98', '99'])).
% 0.21/0.50  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('102', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.50  thf('103', plain,
% 0.21/0.50      ((~ (v2_tex_2 @ sk_B @ sk_A)) <= (~ ((v2_tex_2 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('104', plain, (~ ((v1_zfmisc_1 @ sk_B)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.50  thf('105', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '70', '71', '104'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
