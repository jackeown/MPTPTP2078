%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1271+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CtsDIOc1Ir

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:21 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 328 expanded)
%              Number of leaves         :   22 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          : 1475 (5502 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t90_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_tops_1 @ B @ A )
                  & ( v3_tops_1 @ C @ A ) )
               => ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_tops_1 @ B @ A )
                    & ( v3_tops_1 @ C @ A ) )
                 => ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t90_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_tops_1 @ X3 @ X4 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_pre_topc @ X12 @ ( k2_pre_topc @ X12 @ X13 ) )
        = ( k2_pre_topc @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('15',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
      = ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ( v3_tops_1 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ( v3_tops_1 @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_pre_topc @ X12 @ ( k2_pre_topc @ X12 @ X13 ) )
        = ( k2_pre_topc @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t50_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k2_pre_topc @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X16 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ X14 ) @ ( k2_pre_topc @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_pre_topc @ X12 @ ( k2_pre_topc @ X12 @ X13 ) )
        = ( k2_pre_topc @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','60'])).

thf('62',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t85_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tops_1 @ B @ A )
                  & ( v2_tops_1 @ C @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tops_1 @ X17 @ X18 )
      | ~ ( v2_tops_1 @ X19 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t85_tops_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_tops_1 @ X3 @ X4 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','85'])).

thf('87',plain,
    ( ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v3_tops_1 @ X3 @ X4 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X4 @ X3 ) @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('96',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['87','93','99'])).

thf('101',plain,(
    v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['49','68','69','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ X16 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k2_pre_topc @ X15 @ X14 ) @ ( k2_pre_topc @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    v3_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['101','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['26','110'])).


%------------------------------------------------------------------------------
