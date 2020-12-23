%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uovsf6GbbO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 530 expanded)
%              Number of leaves         :   30 ( 163 expanded)
%              Depth                    :   23
%              Number of atoms          : 1364 (6043 expanded)
%              Number of equality atoms :   24 ( 188 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( ~ ( v1_tdlat_3 @ X36 )
      | ( ( u1_pre_topc @ X36 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf(t17_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v1_tdlat_3 @ A ) )
           => ( v1_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v1_tdlat_3 @ A ) )
             => ( v1_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tex_2])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X31 )
      | ( r1_tarski @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X28: $i] :
      ( ( m1_pre_topc @ X28 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
       => ( v2_pre_topc @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t58_pre_topc])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('34',plain,(
    ! [X35: $i] :
      ( ~ ( v1_tdlat_3 @ X35 )
      | ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('35',plain,
    ( ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['31','32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('40',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','38','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('57',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X36: $i] :
      ( ( ( u1_pre_topc @ X36 )
       != ( k9_setfam_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v1_tdlat_3 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('60',plain,
    ( ( ( u1_pre_topc @ sk_B )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_tops_2 @ X20 @ X21 )
      | ( r1_tarski @ X20 @ ( u1_pre_topc @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('74',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v1_tops_2 @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v1_tops_2 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('82',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( m1_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) ) )
      | ( m1_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_pre_topc @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( r1_tarski @ X20 @ ( u1_pre_topc @ X21 ) )
      | ( v1_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['99','100','102'])).

thf('104',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['78','79','80','81','103'])).

thf('105',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['72','104'])).

thf('106',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_tops_2 @ X20 @ X21 )
      | ( r1_tarski @ X20 @ ( u1_pre_topc @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('119',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('120',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v1_tops_2 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_tops_2 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_A @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('126',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('128',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( r1_tarski @ X20 @ ( u1_pre_topc @ X21 ) )
      | ( v1_tops_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('135',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('138',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['122','123','124','125','138'])).

thf('140',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['117','139'])).

thf('141',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['107','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['60','141','142'])).

thf('144',plain,(
    ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ( u1_pre_topc @ sk_A )
 != ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ( u1_pre_topc @ sk_A )
 != ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    $false ),
    inference(simplify,[status(thm)],['149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Uovsf6GbbO
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:38:08 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 195 iterations in 0.093s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.37/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.37/0.57  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(d1_tdlat_3, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ( v1_tdlat_3 @ A ) <=>
% 0.37/0.57         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X36 : $i]:
% 0.37/0.57         (~ (v1_tdlat_3 @ X36)
% 0.37/0.57          | ((u1_pre_topc @ X36) = (k9_setfam_1 @ (u1_struct_0 @ X36)))
% 0.37/0.57          | ~ (l1_pre_topc @ X36))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.37/0.57  thf(t17_tex_2, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( l1_pre_topc @ B ) =>
% 0.37/0.57           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.57               ( v1_tdlat_3 @ A ) ) =>
% 0.37/0.57             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( l1_pre_topc @ A ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( l1_pre_topc @ B ) =>
% 0.37/0.57              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.57                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.57                  ( v1_tdlat_3 @ A ) ) =>
% 0.37/0.57                ( v1_tdlat_3 @ B ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t17_tex_2])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t2_tsep_1, axiom,
% 0.37/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.57  thf(t65_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( l1_pre_topc @ B ) =>
% 0.37/0.57           ( ( m1_pre_topc @ A @ B ) <=>
% 0.37/0.57             ( m1_pre_topc @
% 0.37/0.57               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X11)
% 0.37/0.57          | ~ (m1_pre_topc @ X12 @ X11)
% 0.37/0.57          | (m1_pre_topc @ X12 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_pre_topc @ X0 @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (((m1_pre_topc @ sk_B @ 
% 0.37/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['1', '5'])).
% 0.37/0.57  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      ((m1_pre_topc @ sk_B @ 
% 0.37/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf(t59_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @
% 0.37/0.57             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.37/0.57           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X9 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.37/0.57          | (m1_pre_topc @ X9 @ X10)
% 0.37/0.57          | ~ (l1_pre_topc @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.57  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('12', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.57  thf(t4_tsep_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.37/0.57               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.37/0.57                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X29 @ X30)
% 0.37/0.57          | ~ (m1_pre_topc @ X29 @ X31)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X31))
% 0.37/0.57          | ~ (m1_pre_topc @ X31 @ X30)
% 0.37/0.57          | ~ (l1_pre_topc @ X30)
% 0.37/0.57          | ~ (v2_pre_topc @ X30))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.37/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ X1)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.37/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_B)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.37/0.57        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '16'])).
% 0.37/0.57  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X28 : $i]: ((m1_pre_topc @ X28 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.37/0.57  thf(t11_tmap_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( ( v1_pre_topc @
% 0.37/0.57               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.57             ( m1_pre_topc @
% 0.37/0.57               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X23 @ X24)
% 0.37/0.57          | (m1_pre_topc @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)) @ X24)
% 0.37/0.57          | ~ (l1_pre_topc @ X24))),
% 0.37/0.57      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (m1_pre_topc @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_pre_topc @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.57  thf(cc1_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X3 @ X4)
% 0.37/0.57          | (v2_pre_topc @ X3)
% 0.37/0.57          | ~ (l1_pre_topc @ X4)
% 0.37/0.57          | ~ (v2_pre_topc @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0)
% 0.37/0.57          | (v2_pre_topc @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v2_pre_topc @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t58_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ( v2_pre_topc @
% 0.37/0.57           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.37/0.57         ( v2_pre_topc @ A ) ) ))).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X8 : $i]:
% 0.37/0.57         (~ (v2_pre_topc @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.37/0.57          | (v2_pre_topc @ X8)
% 0.37/0.57          | ~ (l1_pre_topc @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t58_pre_topc])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      ((~ (v2_pre_topc @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (v2_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      ((~ (v2_pre_topc @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57        | (v2_pre_topc @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A) | ~ (v2_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '30'])).
% 0.37/0.57  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc1_tdlat_3, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X35 : $i]:
% 0.37/0.57         (~ (v1_tdlat_3 @ X35) | (v2_pre_topc @ X35) | ~ (l1_pre_topc @ X35))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.37/0.57  thf('35', plain, (((v2_pre_topc @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain, ((v1_tdlat_3 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['31', '32', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_pre_topc @ X0 @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X9 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.37/0.57          | (m1_pre_topc @ X9 @ X10)
% 0.37/0.57          | ~ (l1_pre_topc @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57          | (m1_pre_topc @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57          | (m1_pre_topc @ X0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['39', '44'])).
% 0.37/0.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18', '38', '47'])).
% 0.37/0.57  thf(d10_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.57        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.57  thf('51', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ X1)
% 0.37/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.37/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.37/0.57          | ~ (v2_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('57', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.37/0.57  thf('58', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['50', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X36 : $i]:
% 0.37/0.57         (((u1_pre_topc @ X36) != (k9_setfam_1 @ (u1_struct_0 @ X36)))
% 0.37/0.57          | (v1_tdlat_3 @ X36)
% 0.37/0.57          | ~ (l1_pre_topc @ X36))),
% 0.37/0.57      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_B) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (v1_tdlat_3 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.57  thf('61', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf(dt_u1_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( m1_subset_1 @
% 0.37/0.57         ( u1_pre_topc @ A ) @ 
% 0.37/0.57         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      (![X7 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.37/0.57          | ~ (l1_pre_topc @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.57  thf(t31_tops_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @
% 0.37/0.57                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.57               ( m1_subset_1 @
% 0.37/0.57                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X13 @ X14)
% 0.37/0.57          | (m1_subset_1 @ X15 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.37/0.57          | ~ (l1_pre_topc @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X1)
% 0.37/0.57          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.37/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['61', '64'])).
% 0.37/0.57  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.57  thf(t78_tops_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @
% 0.37/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.37/0.57          | ~ (v1_tops_2 @ X20 @ X21)
% 0.37/0.57          | (r1_tarski @ X20 @ (u1_pre_topc @ X21))
% 0.37/0.57          | ~ (l1_pre_topc @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.57  thf('70', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.57  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (![X7 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.37/0.57          | ~ (l1_pre_topc @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.57  thf(t35_tops_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @
% 0.37/0.57             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.37/0.57               ( ( v1_tops_2 @ B @ A ) =>
% 0.37/0.57                 ( ![D:$i]:
% 0.37/0.57                   ( ( m1_subset_1 @
% 0.37/0.57                       D @ 
% 0.37/0.57                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.37/0.57                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('75', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.37/0.57          | ~ (v1_tops_2 @ X16 @ X17)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.37/0.57          | (v1_tops_2 @ X18 @ X19)
% 0.37/0.57          | ((X18) != (X16))
% 0.37/0.57          | ~ (m1_pre_topc @ X19 @ X17)
% 0.37/0.57          | ~ (l1_pre_topc @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X17)
% 0.37/0.57          | ~ (m1_pre_topc @ X19 @ X17)
% 0.37/0.57          | (v1_tops_2 @ X16 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.37/0.57          | ~ (v1_tops_2 @ X16 @ X17)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['75'])).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.37/0.57          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.37/0.57          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.37/0.57          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['74', '76'])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['73', '77'])).
% 0.37/0.57  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('82', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('83', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X11)
% 0.37/0.57          | ~ (m1_pre_topc @ X12 @ X11)
% 0.37/0.57          | (m1_pre_topc @ X12 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.37/0.57          | ~ (l1_pre_topc @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (m1_pre_topc @ sk_A @ 
% 0.37/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.57  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('86', plain,
% 0.37/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('88', plain,
% 0.37/0.57      ((m1_pre_topc @ sk_A @ 
% 0.37/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.37/0.57  thf('89', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X9 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10)))
% 0.37/0.57          | (m1_pre_topc @ X9 @ X10)
% 0.37/0.57          | ~ (l1_pre_topc @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.37/0.57  thf('90', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.57  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('92', plain, ((m1_pre_topc @ sk_A @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.37/0.57  thf('93', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X1)
% 0.37/0.57          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.37/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('94', plain,
% 0.37/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.57  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('97', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.57  thf('98', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.37/0.57          | ~ (r1_tarski @ X20 @ (u1_pre_topc @ X21))
% 0.37/0.57          | (v1_tops_2 @ X20 @ X21)
% 0.37/0.57          | ~ (l1_pre_topc @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.57  thf('99', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.37/0.57        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.57  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('101', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('102', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['101'])).
% 0.37/0.57  thf('103', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['99', '100', '102'])).
% 0.37/0.57  thf('104', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['78', '79', '80', '81', '103'])).
% 0.37/0.57  thf('105', plain,
% 0.37/0.57      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['72', '104'])).
% 0.37/0.57  thf('106', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.57  thf('107', plain,
% 0.37/0.57      ((~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['105', '106'])).
% 0.37/0.57  thf('108', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('109', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X1)
% 0.37/0.57          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.37/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('110', plain,
% 0.37/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['108', '109'])).
% 0.37/0.57  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('113', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.37/0.57  thf('114', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.37/0.57          | ~ (v1_tops_2 @ X20 @ X21)
% 0.37/0.57          | (r1_tarski @ X20 @ (u1_pre_topc @ X21))
% 0.37/0.57          | ~ (l1_pre_topc @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.57  thf('115', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.37/0.57  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('117', plain,
% 0.37/0.57      (((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['115', '116'])).
% 0.37/0.57  thf('118', plain,
% 0.37/0.57      (![X7 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.37/0.57          | ~ (l1_pre_topc @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.57  thf('119', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.37/0.57  thf('120', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X17)
% 0.37/0.57          | ~ (m1_pre_topc @ X19 @ X17)
% 0.37/0.57          | (v1_tops_2 @ X16 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.37/0.57          | ~ (v1_tops_2 @ X16 @ X17)
% 0.37/0.57          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['75'])).
% 0.37/0.57  thf('121', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.37/0.57          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ X0)
% 0.37/0.57          | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.37/0.57          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['119', '120'])).
% 0.37/0.57  thf('122', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | ~ (m1_pre_topc @ sk_A @ sk_B)
% 0.37/0.57        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)
% 0.37/0.57        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['118', '121'])).
% 0.37/0.57  thf('123', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('124', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('125', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('126', plain,
% 0.37/0.57      ((m1_pre_topc @ sk_B @ 
% 0.37/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('127', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_pre_topc @ X0 @ 
% 0.37/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.37/0.57          | (m1_pre_topc @ X0 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('128', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.37/0.57      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.57  thf('129', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X0)
% 0.37/0.57          | ~ (l1_pre_topc @ X1)
% 0.37/0.57          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.37/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.37/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('130', plain,
% 0.37/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['128', '129'])).
% 0.37/0.57  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('132', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('133', plain,
% 0.37/0.57      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.57      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.37/0.57  thf('134', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.37/0.57          | ~ (r1_tarski @ X20 @ (u1_pre_topc @ X21))
% 0.37/0.57          | (v1_tops_2 @ X20 @ X21)
% 0.37/0.57          | ~ (l1_pre_topc @ X21))),
% 0.37/0.57      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.57  thf('135', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.57        | (v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)
% 0.37/0.57        | ~ (r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['133', '134'])).
% 0.37/0.57  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('137', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.57      inference('simplify', [status(thm)], ['101'])).
% 0.37/0.57  thf('138', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.37/0.57  thf('139', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['122', '123', '124', '125', '138'])).
% 0.37/0.57  thf('140', plain,
% 0.37/0.57      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['117', '139'])).
% 0.37/0.57  thf('141', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['107', '140'])).
% 0.37/0.57  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('143', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | (v1_tdlat_3 @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['60', '141', '142'])).
% 0.37/0.57  thf('144', plain, (~ (v1_tdlat_3 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('145', plain,
% 0.37/0.57      (((u1_pre_topc @ sk_A) != (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['143', '144'])).
% 0.37/0.57  thf('146', plain,
% 0.37/0.57      ((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v1_tdlat_3 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '145'])).
% 0.37/0.57  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('148', plain, ((v1_tdlat_3 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('149', plain, (((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.37/0.57  thf('150', plain, ($false), inference('simplify', [status(thm)], ['149'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
