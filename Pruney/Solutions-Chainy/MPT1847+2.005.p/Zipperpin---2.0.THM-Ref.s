%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MiJt4MQKgM

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:54 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  305 (2708 expanded)
%              Number of leaves         :   35 ( 806 expanded)
%              Depth                    :   22
%              Number of atoms          : 2310 (32356 expanded)
%              Number of equality atoms :   97 (1204 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tex_2 @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ( v1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_tex_2 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('29',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k1_pre_topc @ X7 @ X6 ) )
      | ( ( k2_struct_0 @ X8 )
        = X6 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('55',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('60',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('64',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52','57','62','63'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['39','64'])).

thf('66',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('70',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('72',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('75',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('77',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('80',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('82',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','77','82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf('87',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( sk_C @ X23 @ X24 )
        = ( u1_struct_0 @ X23 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( sk_C @ sk_C_1 @ sk_A )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_subset_1 @ ( sk_C @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('96',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf('101',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','103'])).

thf('105',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('108',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('114',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','103'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['87','103'])).

thf('119',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('121',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('122',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('123',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('126',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('130',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['128','132'])).

thf('134',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['120','133'])).

thf('135',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf('136',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('141',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('144',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('146',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','144','145'])).

thf('147',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('148',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('158',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('160',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('161',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('166',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('190',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','192'])).

thf('194',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['193','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['187','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['168','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('208',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['206','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ( ( u1_struct_0 @ sk_C_1 )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['158','214'])).

thf('216',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','84','85'])).

thf('217',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('218',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('222',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('224',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('226',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('229',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('230',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('234',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('235',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('239',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227','232','237','238'])).

thf('240',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['219','239'])).

thf('241',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('242',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('243',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('245',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('247',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('249',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['235','236'])).

thf('250',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('252',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('254',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('255',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('257',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['247','252','257','258'])).

thf('260',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('261',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['240','259','260'])).

thf('262',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['156','157','218','261'])).

thf('263',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['119','262'])).

thf('264',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','263'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('265',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('266',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('267',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    $false ),
    inference('sup-',[status(thm)],['264','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MiJt4MQKgM
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.91  % Solved by: fo/fo7.sh
% 0.67/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.91  % done 636 iterations in 0.449s
% 0.67/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.91  % SZS output start Refutation
% 0.67/0.91  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.67/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.91  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.67/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.91  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.67/0.91  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.67/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.91  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.67/0.91  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.67/0.91  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.91  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.67/0.91  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.67/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.91  thf(d3_struct_0, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.91  thf('0', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf(t14_tex_2, conjecture,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.91           ( ![C:$i]:
% 0.67/0.91             ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.91               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.91                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.91                   ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.91                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.91    (~( ![A:$i]:
% 0.67/0.91        ( ( l1_pre_topc @ A ) =>
% 0.67/0.91          ( ![B:$i]:
% 0.67/0.91            ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.91              ( ![C:$i]:
% 0.67/0.91                ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.91                  ( ( ( ( g1_pre_topc @
% 0.67/0.91                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.91                        ( g1_pre_topc @
% 0.67/0.91                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.91                      ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.91                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.67/0.91    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.67/0.91  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t1_tsep_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.91           ( m1_subset_1 @
% 0.67/0.91             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.67/0.91  thf('2', plain,
% 0.67/0.91      (![X19 : $i, X20 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X19 @ X20)
% 0.67/0.91          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.67/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.67/0.91          | ~ (l1_pre_topc @ X20))),
% 0.67/0.91      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.91  thf('3', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.91  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('5', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.91  thf(d3_tex_2, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.91           ( ( v1_tex_2 @ B @ A ) <=>
% 0.67/0.91             ( ![C:$i]:
% 0.67/0.91               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.91                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.67/0.91                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.67/0.91  thf('6', plain,
% 0.67/0.91      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.91          | ~ (v1_tex_2 @ X23 @ X24)
% 0.67/0.91          | ((X25) != (u1_struct_0 @ X23))
% 0.67/0.91          | (v1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.67/0.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.67/0.91          | ~ (l1_pre_topc @ X24))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.91  thf('7', plain,
% 0.67/0.91      (![X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X24)
% 0.67/0.91          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.67/0.91               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.67/0.91          | (v1_subset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.67/0.91          | ~ (v1_tex_2 @ X23 @ X24)
% 0.67/0.91          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.67/0.91      inference('simplify', [status(thm)], ['6'])).
% 0.67/0.91  thf('8', plain,
% 0.67/0.91      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.91        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.67/0.91        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['5', '7'])).
% 0.67/0.91  thf('9', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('10', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('12', plain,
% 0.67/0.91      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.67/0.91  thf('13', plain,
% 0.67/0.91      (((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['0', '12'])).
% 0.67/0.91  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(dt_m1_pre_topc, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.67/0.91  thf('15', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.91          | (l1_pre_topc @ X13)
% 0.67/0.91          | ~ (l1_pre_topc @ X14))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.91  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.91  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf(dt_l1_pre_topc, axiom,
% 0.67/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.67/0.91  thf('19', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('21', plain,
% 0.67/0.91      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['13', '20'])).
% 0.67/0.91  thf('22', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('24', plain,
% 0.67/0.91      (![X19 : $i, X20 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X19 @ X20)
% 0.67/0.91          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.67/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.67/0.91          | ~ (l1_pre_topc @ X20))),
% 0.67/0.91      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.91  thf('25', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.91  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('27', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.91  thf(d7_subset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.91       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.67/0.91  thf('28', plain,
% 0.67/0.91      (![X26 : $i, X27 : $i]:
% 0.67/0.91         (((X27) = (X26))
% 0.67/0.91          | (v1_subset_1 @ X27 @ X26)
% 0.67/0.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.67/0.91      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.67/0.91  thf('29', plain,
% 0.67/0.91      (((v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['27', '28'])).
% 0.67/0.91  thf('30', plain,
% 0.67/0.91      (((v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1)
% 0.67/0.91        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('sup+', [status(thm)], ['22', '29'])).
% 0.67/0.91  thf('31', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('32', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.91          | (l1_pre_topc @ X13)
% 0.67/0.91          | ~ (l1_pre_topc @ X14))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.91  thf('33', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.67/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.67/0.91  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('35', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.91  thf('36', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('37', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('38', plain,
% 0.67/0.91      (((v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ((u1_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['30', '37'])).
% 0.67/0.91  thf('39', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('40', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('41', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.91  thf('42', plain,
% 0.67/0.91      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.91      inference('sup+', [status(thm)], ['40', '41'])).
% 0.67/0.91  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('44', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.91  thf('46', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['42', '45'])).
% 0.67/0.91  thf('47', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf(d10_pre_topc, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.91           ( ![C:$i]:
% 0.67/0.91             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.67/0.91               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.67/0.91                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.67/0.91  thf('48', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.67/0.91          | ((X8) != (k1_pre_topc @ X7 @ X6))
% 0.67/0.91          | ((k2_struct_0 @ X8) = (X6))
% 0.67/0.91          | ~ (m1_pre_topc @ X8 @ X7)
% 0.67/0.91          | ~ (v1_pre_topc @ X8)
% 0.67/0.91          | ~ (l1_pre_topc @ X7))),
% 0.67/0.91      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.67/0.91  thf('49', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X7)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.91  thf('50', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.91  thf('51', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.91        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.91        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.91            = (u1_struct_0 @ sk_C_1))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['46', '50'])).
% 0.67/0.91  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('53', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.91  thf(dt_k1_pre_topc, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( l1_pre_topc @ A ) & 
% 0.67/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.91       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.67/0.91         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.67/0.91  thf('54', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('55', plain,
% 0.67/0.91      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['53', '54'])).
% 0.67/0.91  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('57', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['55', '56'])).
% 0.67/0.91  thf('58', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.91  thf('59', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('60', plain,
% 0.67/0.91      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['58', '59'])).
% 0.67/0.91  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('62', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['60', '61'])).
% 0.67/0.91  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.91  thf('64', plain,
% 0.67/0.91      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 0.67/0.91         = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['51', '52', '57', '62', '63'])).
% 0.67/0.91  thf('65', plain,
% 0.67/0.91      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.91          = (u1_struct_0 @ sk_C_1))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['39', '64'])).
% 0.67/0.91  thf('66', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('67', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.67/0.91  thf('68', plain,
% 0.67/0.91      (((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 0.67/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['66', '67'])).
% 0.67/0.91  thf('69', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('70', plain,
% 0.67/0.91      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['68', '69'])).
% 0.67/0.91  thf('71', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X7)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.91  thf('72', plain,
% 0.67/0.91      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.91          = (k2_struct_0 @ sk_C_1))
% 0.67/0.91        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.91        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.91  thf('73', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('74', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['60', '61'])).
% 0.67/0.91  thf('75', plain,
% 0.67/0.91      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['73', '74'])).
% 0.67/0.91  thf('76', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('77', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['75', '76'])).
% 0.67/0.91  thf('78', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('79', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['55', '56'])).
% 0.67/0.91  thf('80', plain,
% 0.67/0.91      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['78', '79'])).
% 0.67/0.91  thf('81', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('82', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['80', '81'])).
% 0.67/0.91  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('84', plain,
% 0.67/0.91      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 0.67/0.91         = (k2_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['72', '77', '82', '83'])).
% 0.67/0.91  thf('85', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('86', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf('87', plain,
% 0.67/0.91      (((v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['38', '86'])).
% 0.67/0.91  thf('88', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('89', plain,
% 0.67/0.91      (![X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.91          | ((sk_C @ X23 @ X24) = (u1_struct_0 @ X23))
% 0.67/0.91          | (v1_tex_2 @ X23 @ X24)
% 0.67/0.91          | ~ (l1_pre_topc @ X24))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.91  thf('90', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.91        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['88', '89'])).
% 0.67/0.91  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('92', plain,
% 0.67/0.91      (((v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.91        | ((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['90', '91'])).
% 0.67/0.91  thf('93', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('94', plain, (((sk_C @ sk_C_1 @ sk_A) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('clc', [status(thm)], ['92', '93'])).
% 0.67/0.91  thf('95', plain,
% 0.67/0.91      (![X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X23 @ X24)
% 0.67/0.91          | ~ (v1_subset_1 @ (sk_C @ X23 @ X24) @ (u1_struct_0 @ X24))
% 0.67/0.91          | (v1_tex_2 @ X23 @ X24)
% 0.67/0.91          | ~ (l1_pre_topc @ X24))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.91  thf('96', plain,
% 0.67/0.91      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | (v1_tex_2 @ sk_C_1 @ sk_A)
% 0.67/0.91        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['94', '95'])).
% 0.67/0.91  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('98', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('99', plain,
% 0.67/0.91      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.67/0.91  thf('100', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf('101', plain,
% 0.67/0.91      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | (v1_tex_2 @ sk_C_1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['99', '100'])).
% 0.67/0.91  thf('102', plain, (~ (v1_tex_2 @ sk_C_1 @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('103', plain,
% 0.67/0.91      (~ (v1_subset_1 @ (k2_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('clc', [status(thm)], ['101', '102'])).
% 0.67/0.91  thf('104', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('clc', [status(thm)], ['87', '103'])).
% 0.67/0.91  thf('105', plain,
% 0.67/0.91      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['21', '104'])).
% 0.67/0.91  thf('106', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('107', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t35_borsuk_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.91           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.67/0.91  thf('108', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.91          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.91          | ~ (l1_pre_topc @ X22))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.91  thf('109', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['107', '108'])).
% 0.67/0.91  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('111', plain,
% 0.67/0.91      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['109', '110'])).
% 0.67/0.91  thf('112', plain,
% 0.67/0.91      (((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['106', '111'])).
% 0.67/0.91  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('114', plain,
% 0.67/0.91      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['112', '113'])).
% 0.67/0.91  thf(d10_xboole_0, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.91  thf('115', plain,
% 0.67/0.91      (![X0 : $i, X2 : $i]:
% 0.67/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.91  thf('116', plain,
% 0.67/0.91      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.67/0.91        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_B)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['114', '115'])).
% 0.67/0.91  thf('117', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('clc', [status(thm)], ['87', '103'])).
% 0.67/0.91  thf('118', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.67/0.91      inference('clc', [status(thm)], ['87', '103'])).
% 0.67/0.91  thf('119', plain,
% 0.67/0.91      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 0.67/0.91        | ((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.67/0.91  thf('120', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf(dt_k2_subset_1, axiom,
% 0.67/0.91    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.67/0.91  thf('121', plain,
% 0.67/0.91      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.67/0.91  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.67/0.91  thf('122', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.67/0.91      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.91  thf('123', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.91  thf('124', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('125', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.91  thf(t65_pre_topc, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( l1_pre_topc @ B ) =>
% 0.67/0.91           ( ( m1_pre_topc @ A @ B ) <=>
% 0.67/0.91             ( m1_pre_topc @
% 0.67/0.91               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.67/0.91  thf('126', plain,
% 0.67/0.91      (![X17 : $i, X18 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X17)
% 0.67/0.91          | ~ (m1_pre_topc @ X18 @ X17)
% 0.67/0.91          | (m1_pre_topc @ X18 @ 
% 0.67/0.91             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.67/0.91          | ~ (l1_pre_topc @ X18))),
% 0.67/0.91      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.67/0.91  thf('127', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.67/0.91             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['125', '126'])).
% 0.67/0.91  thf('128', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.67/0.91           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['127'])).
% 0.67/0.91  thf('129', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.91  thf('130', plain,
% 0.67/0.91      (![X13 : $i, X14 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X13 @ X14)
% 0.67/0.91          | (l1_pre_topc @ X13)
% 0.67/0.91          | ~ (l1_pre_topc @ X14))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.91  thf('131', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['129', '130'])).
% 0.67/0.91  thf('132', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['131'])).
% 0.67/0.91  thf('133', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.67/0.91             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.67/0.91      inference('clc', [status(thm)], ['128', '132'])).
% 0.67/0.91  thf('134', plain,
% 0.67/0.91      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ 
% 0.67/0.91         (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['120', '133'])).
% 0.67/0.91  thf('135', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf('136', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('137', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('138', plain,
% 0.67/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91         = (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('139', plain,
% 0.67/0.91      ((((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91          = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['137', '138'])).
% 0.67/0.91  thf('140', plain, ((l1_struct_0 @ sk_C_1)),
% 0.67/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.91  thf('141', plain,
% 0.67/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.91  thf('142', plain,
% 0.67/0.91      ((((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91          = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['136', '141'])).
% 0.67/0.91  thf('143', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('144', plain,
% 0.67/0.91      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['142', '143'])).
% 0.67/0.91  thf('145', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.91  thf('146', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ 
% 0.67/0.91        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['134', '135', '144', '145'])).
% 0.67/0.91  thf('147', plain,
% 0.67/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['139', '140'])).
% 0.67/0.91  thf(t59_pre_topc, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( l1_pre_topc @ A ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( m1_pre_topc @
% 0.67/0.91             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.67/0.91           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.67/0.91  thf('148', plain,
% 0.67/0.91      (![X15 : $i, X16 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X15 @ 
% 0.67/0.91             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.67/0.91          | (m1_pre_topc @ X15 @ X16)
% 0.67/0.91          | ~ (l1_pre_topc @ X16))),
% 0.67/0.91      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.67/0.91  thf('149', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.91             (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.91          | ~ (l1_pre_topc @ sk_B)
% 0.67/0.91          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['147', '148'])).
% 0.67/0.91  thf('150', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf('151', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.91             (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.67/0.91          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['149', '150'])).
% 0.67/0.91  thf('152', plain,
% 0.67/0.91      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.91         = (g1_pre_topc @ (k2_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.67/0.91      inference('demod', [status(thm)], ['142', '143'])).
% 0.67/0.91  thf('153', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.91             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.67/0.91          | (m1_pre_topc @ X0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['151', '152'])).
% 0.67/0.91  thf('154', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1)) @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['146', '153'])).
% 0.67/0.91  thf('155', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.91          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.91          | ~ (l1_pre_topc @ X22))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.91  thf('156', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_B)
% 0.67/0.91        | (r1_tarski @ 
% 0.67/0.91           (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))) @ 
% 0.67/0.91           (u1_struct_0 @ sk_B)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['154', '155'])).
% 0.67/0.91  thf('157', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf('158', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf('159', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.91  thf('160', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.91  thf('161', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X7)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.91  thf('162', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91            = (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['160', '161'])).
% 0.67/0.91  thf('163', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91              = (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['159', '162'])).
% 0.67/0.91  thf('164', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91            = (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['163'])).
% 0.67/0.91  thf('165', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.91  thf('166', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('167', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.91  thf('168', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91              = (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('clc', [status(thm)], ['164', '167'])).
% 0.67/0.91  thf('169', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('170', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.91  thf('171', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup+', [status(thm)], ['169', '170'])).
% 0.67/0.91  thf('172', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('173', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 0.67/0.91      inference('clc', [status(thm)], ['171', '172'])).
% 0.67/0.91  thf('174', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('175', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.91  thf('176', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup+', [status(thm)], ['174', '175'])).
% 0.67/0.91  thf('177', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('178', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.67/0.91      inference('clc', [status(thm)], ['176', '177'])).
% 0.67/0.91  thf('179', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['121', '122'])).
% 0.67/0.91  thf('180', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.91  thf('181', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91              = (k2_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_struct_0 @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['179', '180'])).
% 0.67/0.91  thf('182', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91              = (k2_struct_0 @ X0))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['178', '181'])).
% 0.67/0.91  thf('183', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91              = (k2_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['182'])).
% 0.67/0.91  thf('184', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91              = (k2_struct_0 @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['173', '183'])).
% 0.67/0.91  thf('185', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91            = (k2_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['184'])).
% 0.67/0.91  thf('186', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('187', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91              = (k2_struct_0 @ X0)))),
% 0.67/0.91      inference('clc', [status(thm)], ['185', '186'])).
% 0.67/0.91  thf('188', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('189', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 0.67/0.91      inference('clc', [status(thm)], ['171', '172'])).
% 0.67/0.91  thf('190', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.91          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.91          | ~ (l1_pre_topc @ X22))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.91  thf('191', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | (r1_tarski @ 
% 0.67/0.91             (u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.91             (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['189', '190'])).
% 0.67/0.91  thf('192', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((r1_tarski @ 
% 0.67/0.91           (u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.91           (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['191'])).
% 0.67/0.91  thf('193', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((r1_tarski @ 
% 0.67/0.91           (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.91           (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup+', [status(thm)], ['188', '192'])).
% 0.67/0.91  thf('194', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('195', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['131'])).
% 0.67/0.91  thf('196', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup+', [status(thm)], ['194', '195'])).
% 0.67/0.91  thf('197', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('198', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.67/0.91      inference('clc', [status(thm)], ['196', '197'])).
% 0.67/0.91  thf('199', plain,
% 0.67/0.91      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.91  thf('200', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (l1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['198', '199'])).
% 0.67/0.91  thf('201', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (r1_tarski @ 
% 0.67/0.91             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.67/0.91             (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('clc', [status(thm)], ['193', '200'])).
% 0.67/0.91  thf('202', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup+', [status(thm)], ['187', '201'])).
% 0.67/0.91  thf('203', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['202'])).
% 0.67/0.91  thf('204', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.91           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.67/0.91      inference('sup+', [status(thm)], ['168', '203'])).
% 0.67/0.91  thf('205', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['131'])).
% 0.67/0.91  thf('206', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.91             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.67/0.91      inference('clc', [status(thm)], ['204', '205'])).
% 0.67/0.91  thf('207', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '124'])).
% 0.67/0.91  thf('208', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i]:
% 0.67/0.91         (~ (m1_pre_topc @ X21 @ X22)
% 0.67/0.91          | (r1_tarski @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.67/0.91          | ~ (l1_pre_topc @ X22))),
% 0.67/0.91      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.67/0.91  thf('209', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (l1_pre_topc @ X0)
% 0.67/0.91          | (r1_tarski @ 
% 0.67/0.91             (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.91             (u1_struct_0 @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['207', '208'])).
% 0.67/0.91  thf('210', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((r1_tarski @ 
% 0.67/0.91           (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.67/0.91           (u1_struct_0 @ X0))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['209'])).
% 0.67/0.91  thf('211', plain,
% 0.67/0.91      (![X0 : $i, X2 : $i]:
% 0.67/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.91  thf('212', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.67/0.91               (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.91          | ((u1_struct_0 @ X0)
% 0.67/0.91              = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['210', '211'])).
% 0.67/0.91  thf('213', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X0)
% 0.67/0.91          | ((u1_struct_0 @ X0)
% 0.67/0.91              = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['206', '212'])).
% 0.67/0.91  thf('214', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((u1_struct_0 @ X0)
% 0.67/0.91            = (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['213'])).
% 0.67/0.91  thf('215', plain,
% 0.67/0.91      ((((u1_struct_0 @ sk_C_1)
% 0.67/0.91          = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_C_1))),
% 0.67/0.91      inference('sup+', [status(thm)], ['158', '214'])).
% 0.67/0.91  thf('216', plain, (((k2_struct_0 @ sk_C_1) = (u1_struct_0 @ sk_C_1))),
% 0.67/0.91      inference('demod', [status(thm)], ['65', '84', '85'])).
% 0.67/0.91  thf('217', plain, ((l1_pre_topc @ sk_C_1)),
% 0.67/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.67/0.91  thf('218', plain,
% 0.67/0.91      (((k2_struct_0 @ sk_C_1)
% 0.67/0.91         = (u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ (k2_struct_0 @ sk_C_1))))),
% 0.67/0.91      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.67/0.91  thf('219', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('220', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('221', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.91  thf('222', plain,
% 0.67/0.91      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.91      inference('sup+', [status(thm)], ['220', '221'])).
% 0.67/0.91  thf('223', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.91  thf('224', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['222', '223'])).
% 0.67/0.91  thf('225', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.67/0.91          | ~ (l1_struct_0 @ X0)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.67/0.91          | ~ (l1_pre_topc @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['47', '49'])).
% 0.67/0.91  thf('226', plain,
% 0.67/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.91        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.91        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.91        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.91            = (u1_struct_0 @ sk_B))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['224', '225'])).
% 0.67/0.91  thf('227', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('228', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.91  thf('229', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (v1_pre_topc @ (k1_pre_topc @ X10 @ X11)))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('230', plain,
% 0.67/0.91      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['228', '229'])).
% 0.67/0.91  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('232', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['230', '231'])).
% 0.67/0.91  thf('233', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.91  thf('234', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X10)
% 0.67/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.67/0.91          | (m1_pre_topc @ (k1_pre_topc @ X10 @ X11) @ X10))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.67/0.91  thf('235', plain,
% 0.67/0.91      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['233', '234'])).
% 0.67/0.91  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('237', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['235', '236'])).
% 0.67/0.91  thf('238', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.91  thf('239', plain,
% 0.67/0.91      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.91         = (u1_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['226', '227', '232', '237', '238'])).
% 0.67/0.91  thf('240', plain,
% 0.67/0.91      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.91          = (u1_struct_0 @ sk_B))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['219', '239'])).
% 0.67/0.91  thf('241', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('242', plain,
% 0.67/0.91      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4'])).
% 0.67/0.91  thf('243', plain,
% 0.67/0.91      (((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['241', '242'])).
% 0.67/0.91  thf('244', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('245', plain,
% 0.67/0.91      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['243', '244'])).
% 0.67/0.91  thf('246', plain,
% 0.67/0.91      (![X6 : $i, X7 : $i]:
% 0.67/0.91         (~ (l1_pre_topc @ X7)
% 0.67/0.91          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.67/0.91          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.67/0.91          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.67/0.91          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['48'])).
% 0.67/0.91  thf('247', plain,
% 0.67/0.91      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.91          = (k2_struct_0 @ sk_B))
% 0.67/0.91        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.91        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.91      inference('sup-', [status(thm)], ['245', '246'])).
% 0.67/0.91  thf('248', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('249', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['235', '236'])).
% 0.67/0.91  thf('250', plain,
% 0.67/0.91      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['248', '249'])).
% 0.67/0.91  thf('251', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('252', plain,
% 0.67/0.91      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['250', '251'])).
% 0.67/0.91  thf('253', plain,
% 0.67/0.91      (![X9 : $i]:
% 0.67/0.91         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.91  thf('254', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['230', '231'])).
% 0.67/0.91  thf('255', plain,
% 0.67/0.91      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.91        | ~ (l1_struct_0 @ sk_B))),
% 0.67/0.91      inference('sup+', [status(thm)], ['253', '254'])).
% 0.67/0.91  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('257', plain,
% 0.67/0.91      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)], ['255', '256'])).
% 0.67/0.91  thf('258', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('259', plain,
% 0.67/0.91      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.67/0.91         = (k2_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['247', '252', '257', '258'])).
% 0.67/0.91  thf('260', plain, ((l1_struct_0 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('261', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['240', '259', '260'])).
% 0.67/0.91  thf('262', plain,
% 0.67/0.91      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['156', '157', '218', '261'])).
% 0.67/0.91  thf('263', plain, (((k2_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['119', '262'])).
% 0.67/0.91  thf('264', plain,
% 0.67/0.91      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['105', '263'])).
% 0.67/0.91  thf(fc14_subset_1, axiom,
% 0.67/0.91    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.67/0.91  thf('265', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.67/0.91      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.67/0.91  thf('266', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.67/0.91      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.91  thf('267', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.67/0.91      inference('demod', [status(thm)], ['265', '266'])).
% 0.67/0.91  thf('268', plain, ($false), inference('sup-', [status(thm)], ['264', '267'])).
% 0.67/0.91  
% 0.67/0.91  % SZS output end Refutation
% 0.67/0.91  
% 0.67/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
