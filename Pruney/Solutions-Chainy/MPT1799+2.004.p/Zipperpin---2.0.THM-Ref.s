%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tCoLeaIM13

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 231 expanded)
%              Number of leaves         :   24 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  904 (3979 expanded)
%              Number of equality atoms :   24 ( 119 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ X7 @ X6 ) )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v3_pre_topc @ X11 @ X10 )
      | ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X9 ) @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X2 @ X3 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X2 @ X3 ) ) ) ),
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
    m1_pre_topc @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('56',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X7 @ X6 ) )
        = ( k5_tmap_1 @ X7 @ X8 ) )
      | ( X8
       != ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t114_tmap_1])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X7 @ X6 ) )
        = ( k5_tmap_1 @ X7 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( u1_pre_topc @ ( k8_tmap_1 @ X0 @ sk_B ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( r2_hidden @ X4 @ ( k5_tmap_1 @ X5 @ X4 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C ) @ ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','72','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['47','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tCoLeaIM13
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 98 iterations in 0.062s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(t115_tmap_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.20/0.51               ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                 ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.51                   ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) =>
% 0.20/0.51                  ( ( ( u1_struct_0 @ C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                    ( ( v1_tsep_1 @ C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.51                      ( m1_pre_topc @ C @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t115_tmap_1])).
% 0.20/0.51  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.51  thf('6', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t114_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ( ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                   ( ( u1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) =
% 0.20/0.51                     ( k5_tmap_1 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X6)
% 0.20/0.51          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.51          | ((u1_struct_0 @ (k8_tmap_1 @ X7 @ X6)) = (u1_struct_0 @ X7))
% 0.20/0.51          | ~ (l1_pre_topc @ X7)
% 0.20/0.51          | ~ (v2_pre_topc @ X7)
% 0.20/0.51          | (v2_struct_0 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.51  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(t16_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.51                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.51          | ((X11) != (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (v3_pre_topc @ X11 @ X10)
% 0.20/0.51          | (v1_tsep_1 @ X9 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.51          | ~ (l1_pre_topc @ X10)
% 0.20/0.51          | ~ (v2_pre_topc @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (v2_pre_topc @ X10)
% 0.20/0.51          | ~ (l1_pre_topc @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.51          | (v1_tsep_1 @ X9 @ X10)
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ X9) @ X10)
% 0.20/0.51          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k8_tmap_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.51         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.20/0.51         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X2)
% 0.20/0.51          | ~ (v2_pre_topc @ X2)
% 0.20/0.51          | (v2_struct_0 @ X2)
% 0.20/0.51          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.51          | (l1_pre_topc @ (k8_tmap_1 @ X2 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.51  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X2)
% 0.20/0.51          | ~ (v2_pre_topc @ X2)
% 0.20/0.51          | (v2_struct_0 @ X2)
% 0.20/0.51          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.51          | (v2_pre_topc @ (k8_tmap_1 @ X2 @ X3)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.51  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51          | (v1_tsep_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '26', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '35'])).
% 0.20/0.51  thf('37', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['39'])).
% 0.20/0.51  thf('41', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((~ (m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= (~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['39'])).
% 0.20/0.51  thf('43', plain, (((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.20/0.51       ~ ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['39'])).
% 0.20/0.51  thf('45', plain, (~ ((v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (~ (v1_tsep_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['40', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['38', '46'])).
% 0.20/0.51  thf('48', plain, ((m1_pre_topc @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf(d5_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.51             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.51          | (v3_pre_topc @ X0 @ X1)
% 0.20/0.51          | ~ (l1_pre_topc @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.51  thf('58', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X6)
% 0.20/0.51          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51          | ((u1_pre_topc @ (k8_tmap_1 @ X7 @ X6)) = (k5_tmap_1 @ X7 @ X8))
% 0.20/0.51          | ((X8) != (u1_struct_0 @ X6))
% 0.20/0.51          | ~ (l1_pre_topc @ X7)
% 0.20/0.51          | ~ (v2_pre_topc @ X7)
% 0.20/0.51          | (v2_struct_0 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t114_tmap_1])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X7)
% 0.20/0.51          | ~ (v2_pre_topc @ X7)
% 0.20/0.51          | ~ (l1_pre_topc @ X7)
% 0.20/0.51          | ((u1_pre_topc @ (k8_tmap_1 @ X7 @ X6))
% 0.20/0.51              = (k5_tmap_1 @ X7 @ (u1_struct_0 @ X6)))
% 0.20/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X6) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.51          | ~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.51          | (v2_struct_0 @ X6))),
% 0.20/0.51      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.51          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.20/0.51              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '60'])).
% 0.20/0.51  thf('62', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.51          | ((u1_pre_topc @ (k8_tmap_1 @ X0 @ sk_B))
% 0.20/0.51              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ sk_C)))
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.20/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '63'])).
% 0.20/0.51  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.51  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51            = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (((u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.20/0.51         = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.51  thf(t102_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.51          | (r2_hidden @ X4 @ (k5_tmap_1 @ X5 @ X4))
% 0.20/0.51          | ~ (l1_pre_topc @ X5)
% 0.20/0.51          | ~ (v2_pre_topc @ X5)
% 0.20/0.51          | (v2_struct_0 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51           (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.20/0.51  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((r2_hidden @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '72', '80'])).
% 0.20/0.51  thf('82', plain, ($false), inference('demod', [status(thm)], ['47', '81'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
