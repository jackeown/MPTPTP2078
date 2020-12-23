%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wy3KDWMkAb

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 187 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  755 (2197 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

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
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X12 @ X11 ) @ X12 )
      | ( v1_zfmisc_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v7_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('8',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('14',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('16',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v7_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('35',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf(cc13_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v7_struct_0 @ X5 )
      | ( v1_tex_2 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v7_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc13_tex_2])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('51',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','55'])).

thf('57',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v7_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wy3KDWMkAb
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 37 iterations in 0.023s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.23/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.49  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.23/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.23/0.49  thf(t20_tex_2, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.23/0.49             ( v1_subset_1 @
% 0.23/0.49               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49          ( ![B:$i]:
% 0.23/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.23/0.49                ( v1_subset_1 @
% 0.23/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.23/0.49                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49           (u1_struct_0 @ sk_A))
% 0.23/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (~
% 0.23/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A))) | 
% 0.23/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t7_tex_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ A ) =>
% 0.23/0.49           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X11 : $i, X12 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X11 @ X12)
% 0.23/0.49          | (v1_subset_1 @ (k6_domain_1 @ X12 @ X11) @ X12)
% 0.23/0.49          | (v1_zfmisc_1 @ X12)
% 0.23/0.49          | (v1_xboole_0 @ X12))),
% 0.23/0.49      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.49        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.23/0.49        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49           (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49           (u1_struct_0 @ sk_A)))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.23/0.49         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf(fc6_struct_0, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.49       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X2 : $i]:
% 0.23/0.49         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X2))
% 0.23/0.49          | ~ (l1_struct_0 @ X2)
% 0.23/0.49          | (v7_struct_0 @ X2))),
% 0.23/0.49      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.49         | (v7_struct_0 @ sk_A)
% 0.23/0.49         | ~ (l1_struct_0 @ sk_A)))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.49  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(dt_l1_pre_topc, axiom,
% 0.23/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.49  thf('10', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.49  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v7_struct_0 @ sk_A)))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.49  thf(fc2_struct_0, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X1 : $i]:
% 0.23/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.23/0.49          | ~ (l1_struct_0 @ X1)
% 0.23/0.49          | (v2_struct_0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.49  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.49  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (((v7_struct_0 @ sk_A))
% 0.23/0.49         <= (~
% 0.23/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.23/0.49  thf('19', plain,
% 0.23/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A))
% 0.23/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.23/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('split', [status(esa)], ['19'])).
% 0.23/0.49  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(dt_k1_tex_2, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.23/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.23/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.49         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.23/0.49  thf('22', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]:
% 0.23/0.49         (~ (l1_pre_topc @ X7)
% 0.23/0.49          | (v2_struct_0 @ X7)
% 0.23/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.23/0.49          | (m1_pre_topc @ (k1_tex_2 @ X7 @ X8) @ X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.49  thf('23', plain,
% 0.23/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.49        | (v2_struct_0 @ sk_A)
% 0.23/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.49  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('25', plain,
% 0.23/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('27', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.49  thf(cc10_tex_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.49           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.23/0.49             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.23/0.49  thf('28', plain,
% 0.23/0.49      (![X3 : $i, X4 : $i]:
% 0.23/0.49         (~ (m1_pre_topc @ X3 @ X4)
% 0.23/0.49          | ~ (v1_tex_2 @ X3 @ X4)
% 0.23/0.49          | (v2_struct_0 @ X3)
% 0.23/0.49          | ~ (l1_pre_topc @ X4)
% 0.23/0.49          | ~ (v7_struct_0 @ X4)
% 0.23/0.49          | (v2_struct_0 @ X4))),
% 0.23/0.49      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.23/0.49  thf('29', plain,
% 0.23/0.49      (((v2_struct_0 @ sk_A)
% 0.23/0.49        | ~ (v7_struct_0 @ sk_A)
% 0.23/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('31', plain,
% 0.23/0.49      (((v2_struct_0 @ sk_A)
% 0.23/0.49        | ~ (v7_struct_0 @ sk_A)
% 0.23/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.49  thf('32', plain,
% 0.23/0.49      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49         | ~ (v7_struct_0 @ sk_A)
% 0.23/0.49         | (v2_struct_0 @ sk_A)))
% 0.23/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['20', '31'])).
% 0.23/0.49  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('34', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]:
% 0.23/0.49         (~ (l1_pre_topc @ X7)
% 0.23/0.49          | (v2_struct_0 @ X7)
% 0.23/0.49          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.23/0.49          | ~ (v2_struct_0 @ (k1_tex_2 @ X7 @ X8)))),
% 0.23/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.49  thf('35', plain,
% 0.23/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | (v2_struct_0 @ sk_A)
% 0.23/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.49  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('37', plain,
% 0.23/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.49  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('39', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.23/0.49  thf('40', plain,
% 0.23/0.49      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.23/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('clc', [status(thm)], ['32', '39'])).
% 0.23/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('42', plain,
% 0.23/0.49      ((~ (v7_struct_0 @ sk_A))
% 0.23/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.23/0.49  thf('43', plain,
% 0.23/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A))) | 
% 0.23/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['18', '42'])).
% 0.23/0.49  thf('44', plain,
% 0.23/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A))) | 
% 0.23/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('split', [status(esa)], ['19'])).
% 0.23/0.49  thf('45', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.49  thf(cc13_tex_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.23/0.49         ( l1_pre_topc @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.49           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) =>
% 0.23/0.49             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) ) ) ) ))).
% 0.23/0.49  thf('46', plain,
% 0.23/0.49      (![X5 : $i, X6 : $i]:
% 0.23/0.49         (~ (m1_pre_topc @ X5 @ X6)
% 0.23/0.49          | ~ (v7_struct_0 @ X5)
% 0.23/0.49          | (v1_tex_2 @ X5 @ X6)
% 0.23/0.49          | (v2_struct_0 @ X5)
% 0.23/0.49          | ~ (l1_pre_topc @ X6)
% 0.23/0.49          | (v7_struct_0 @ X6)
% 0.23/0.49          | (v2_struct_0 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [cc13_tex_2])).
% 0.23/0.49  thf('47', plain,
% 0.23/0.49      (((v2_struct_0 @ sk_A)
% 0.23/0.49        | (v7_struct_0 @ sk_A)
% 0.23/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.49        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.23/0.49  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(fc2_tex_2, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.23/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.23/0.49         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.23/0.49  thf('50', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i]:
% 0.23/0.49         (~ (l1_pre_topc @ X9)
% 0.23/0.49          | (v2_struct_0 @ X9)
% 0.23/0.49          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.23/0.49          | (v7_struct_0 @ (k1_tex_2 @ X9 @ X10)))),
% 0.23/0.49      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.23/0.49  thf('51', plain,
% 0.23/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | (v2_struct_0 @ sk_A)
% 0.23/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.49  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('53', plain,
% 0.23/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.23/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('55', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.23/0.49  thf('56', plain,
% 0.23/0.49      (((v2_struct_0 @ sk_A)
% 0.23/0.49        | (v7_struct_0 @ sk_A)
% 0.23/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['47', '48', '55'])).
% 0.23/0.49  thf('57', plain,
% 0.23/0.49      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.23/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('58', plain,
% 0.23/0.49      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.49         | (v7_struct_0 @ sk_A)
% 0.23/0.49         | (v2_struct_0 @ sk_A)))
% 0.23/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.23/0.49  thf('59', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.23/0.49  thf('60', plain,
% 0.23/0.49      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.23/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('clc', [status(thm)], ['58', '59'])).
% 0.23/0.49  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('62', plain,
% 0.23/0.49      (((v7_struct_0 @ sk_A))
% 0.23/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.23/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.23/0.49  thf('63', plain,
% 0.23/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A)))
% 0.23/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('split', [status(esa)], ['19'])).
% 0.23/0.49  thf(t8_tex_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49           ( ~( ( v1_subset_1 @
% 0.23/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.23/0.49                  ( u1_struct_0 @ A ) ) & 
% 0.23/0.49                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.49  thf('64', plain,
% 0.23/0.49      (![X13 : $i, X14 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.23/0.49          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X14) @ X13) @ 
% 0.23/0.49               (u1_struct_0 @ X14))
% 0.23/0.49          | ~ (v7_struct_0 @ X14)
% 0.23/0.49          | ~ (l1_struct_0 @ X14)
% 0.23/0.49          | (v2_struct_0 @ X14))),
% 0.23/0.49      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.23/0.49  thf('65', plain,
% 0.23/0.49      ((((v2_struct_0 @ sk_A)
% 0.23/0.49         | ~ (l1_struct_0 @ sk_A)
% 0.23/0.49         | ~ (v7_struct_0 @ sk_A)
% 0.23/0.49         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.23/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.23/0.49  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('68', plain,
% 0.23/0.49      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.23/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.23/0.49  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('70', plain,
% 0.23/0.49      ((~ (v7_struct_0 @ sk_A))
% 0.23/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49               (u1_struct_0 @ sk_A))))),
% 0.23/0.49      inference('clc', [status(thm)], ['68', '69'])).
% 0.23/0.49  thf('71', plain,
% 0.23/0.49      (~
% 0.23/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.49         (u1_struct_0 @ sk_A))) | 
% 0.23/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['62', '70'])).
% 0.23/0.49  thf('72', plain, ($false),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '71'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
