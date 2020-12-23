%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kk9ftUYHsK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 316 expanded)
%              Number of leaves         :   27 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          : 1174 (5597 expanded)
%              Number of equality atoms :   44 ( 187 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t115_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
             => ( ( ( u1_struct_0 @ C )
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                  & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) )
               => ( ( ( u1_struct_0 @ C )
                    = ( u1_struct_0 @ B ) )
                 => ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) )
                    & ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t114_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
                    = ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ( v1_tsep_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_tsep_1 @ X13 @ X14 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tsep_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('21',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('29',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tsep_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','26','34'])).

thf('36',plain,
    ( ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('45',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_tsep_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['40','45'])).

thf('47',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X6 @ X5 ) )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(t105_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) )
             => ( ( C = B )
               => ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X9 != X7 )
      | ( v3_pre_topc @ X9 @ ( k6_tmap_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X8 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t105_tmap_1])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ X8 @ X7 ) ) ) )
      | ( v3_pre_topc @ X7 @ ( k6_tmap_1 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(d9_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k6_tmap_1 @ A @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k6_tmap_1 @ X2 @ X1 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( k5_tmap_1 @ X2 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( k5_tmap_1 @ X11 @ X12 ) )
      | ( X12
       != ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
        = ( k5_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('93',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('95',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('97',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94','102'])).

thf('104',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','103'])).

thf('105',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['47','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kk9ftUYHsK
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 86 iterations in 0.080s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.21/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.55  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.55  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(t115_tmap_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.21/0.55               ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.55                 ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.55                   ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.21/0.55                  ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.55                    ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.55                      ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t115_tmap_1])).
% 0.21/0.55  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t1_tsep_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.55           ( m1_subset_1 @
% 0.21/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.55          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.55          | ~ (l1_pre_topc @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('4', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t114_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.55             ( ![C:$i]:
% 0.21/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.55                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.21/0.55                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X10)
% 0.21/0.55          | ~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.55          | ((u1_struct_0 @ (k8_tmap_1 @ X11 @ X10)) = (u1_struct_0 @ X11))
% 0.21/0.55          | ~ (l1_pre_topc @ X11)
% 0.21/0.55          | ~ (v2_pre_topc @ X11)
% 0.21/0.55          | (v2_struct_0 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.55  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_B)
% 0.21/0.55        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf(t16_tsep_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.55                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.55                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.55          | ((X15) != (u1_struct_0 @ X13))
% 0.21/0.55          | ~ (v3_pre_topc @ X15 @ X14)
% 0.21/0.55          | (v1_tsep_1 @ X13 @ X14)
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | ~ (l1_pre_topc @ X14)
% 0.21/0.55          | ~ (v2_pre_topc @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i]:
% 0.21/0.55         (~ (v2_pre_topc @ X14)
% 0.21/0.55          | ~ (l1_pre_topc @ X14)
% 0.21/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | (v1_tsep_1 @ X13 @ X14)
% 0.21/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ X13) @ X14)
% 0.21/0.55          | ~ (m1_pre_topc @ X13 @ X14))),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.55  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_k8_tmap_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.55       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.55         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.55         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X3)
% 0.21/0.55          | ~ (v2_pre_topc @ X3)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (m1_pre_topc @ X4 @ X3)
% 0.21/0.55          | (l1_pre_topc @ (k8_tmap_1 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.55  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('26', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X3)
% 0.21/0.55          | ~ (v2_pre_topc @ X3)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (m1_pre_topc @ X4 @ X3)
% 0.21/0.55          | (v2_pre_topc @ (k8_tmap_1 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.55  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('34', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '26', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '35'])).
% 0.21/0.55  thf('37', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('41', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('43', plain, (((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.21/0.55       ~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('45', plain, (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf('46', plain, (~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['40', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['38', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf(t104_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.55             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.55          | ((u1_struct_0 @ (k6_tmap_1 @ X6 @ X5)) = (u1_struct_0 @ X6))
% 0.21/0.55          | ~ (l1_pre_topc @ X6)
% 0.21/0.55          | ~ (v2_pre_topc @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55            = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55            = (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55         = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf(t105_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @
% 0.21/0.55                 C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) =>
% 0.21/0.55               ( ( ( C ) = ( B ) ) =>
% 0.21/0.55                 ( v3_pre_topc @ C @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.55          | ((X9) != (X7))
% 0.21/0.55          | (v3_pre_topc @ X9 @ (k6_tmap_1 @ X8 @ X7))
% 0.21/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X8 @ X7))))
% 0.21/0.55          | ~ (l1_pre_topc @ X8)
% 0.21/0.55          | ~ (v2_pre_topc @ X8)
% 0.21/0.55          | (v2_struct_0 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t105_tmap_1])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X8)
% 0.21/0.55          | ~ (v2_pre_topc @ X8)
% 0.21/0.55          | ~ (l1_pre_topc @ X8)
% 0.21/0.55          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ X8 @ X7))))
% 0.21/0.55          | (v3_pre_topc @ X7 @ (k6_tmap_1 @ X8 @ X7))
% 0.21/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      ((~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55         (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.21/0.55  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf(d9_tmap_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( k6_tmap_1 @ A @ B ) =
% 0.21/0.55             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.55          | ((k6_tmap_1 @ X2 @ X1)
% 0.21/0.55              = (g1_pre_topc @ (u1_struct_0 @ X2) @ (k5_tmap_1 @ X2 @ X1)))
% 0.21/0.55          | ~ (l1_pre_topc @ X2)
% 0.21/0.55          | ~ (v2_pre_topc @ X2)
% 0.21/0.55          | (v2_struct_0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))
% 0.21/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))
% 0.21/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55               (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.55  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))
% 0.21/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55            (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.21/0.55      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.55  thf('75', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X10)
% 0.21/0.55          | ~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.55          | ((u1_pre_topc @ (k8_tmap_1 @ X11 @ X10)) = (k5_tmap_1 @ X11 @ X12))
% 0.21/0.55          | ((X12) != (u1_struct_0 @ X10))
% 0.21/0.55          | ~ (l1_pre_topc @ X11)
% 0.21/0.55          | ~ (v2_pre_topc @ X11)
% 0.21/0.55          | (v2_struct_0 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X11)
% 0.21/0.55          | ~ (v2_pre_topc @ X11)
% 0.21/0.55          | ~ (l1_pre_topc @ X11)
% 0.21/0.55          | ((u1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.21/0.55              = (k5_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.21/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.55          | ~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.55          | (v2_struct_0 @ X10))),
% 0.21/0.55      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.55          | (v2_struct_0 @ sk_B)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.55          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.21/0.55              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_B)))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '77'])).
% 0.21/0.55  thf('79', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.55          | (v2_struct_0 @ sk_B)
% 0.21/0.55          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.55          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.21/0.55              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_C)))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['74', '80'])).
% 0.21/0.55  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.21/0.55        | (v2_struct_0 @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.21/0.55  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_B)
% 0.21/0.55        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.21/0.55      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.55  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['87', '88'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      (((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))
% 0.21/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['73', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ( v1_pre_topc @ A ) =>
% 0.21/0.55         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.55  thf('92', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_pre_topc @ X0)
% 0.21/0.55          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.55  thf('93', plain,
% 0.21/0.55      ((((k8_tmap_1 @ sk_A @ sk_B)
% 0.21/0.55          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.21/0.55        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('95', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('96', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X3)
% 0.21/0.55          | ~ (v2_pre_topc @ X3)
% 0.21/0.55          | (v2_struct_0 @ X3)
% 0.21/0.55          | ~ (m1_pre_topc @ X4 @ X3)
% 0.21/0.55          | (v1_pre_topc @ (k8_tmap_1 @ X3 @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('100', plain,
% 0.21/0.55      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.21/0.55  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('102', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('103', plain,
% 0.21/0.55      (((k8_tmap_1 @ sk_A @ sk_B)
% 0.21/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55            (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['93', '94', '102'])).
% 0.21/0.55  thf('104', plain,
% 0.21/0.55      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['90', '103'])).
% 0.21/0.55  thf('105', plain,
% 0.21/0.55      ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['65', '104'])).
% 0.21/0.55  thf('106', plain, ($false), inference('demod', [status(thm)], ['47', '105'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
