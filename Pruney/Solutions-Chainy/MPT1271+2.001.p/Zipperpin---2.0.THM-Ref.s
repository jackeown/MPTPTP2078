%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TGY3LKppLh

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 124 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  714 (1946 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X9 @ X8 ) @ X9 )
      | ( v3_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v3_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tops_1 @ X12 @ X13 )
      | ~ ( v2_tops_1 @ X14 @ X13 )
      | ~ ( v4_pre_topc @ X14 @ X13 )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t85_tops_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_tops_1 @ X8 @ X9 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X9 @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','30'])).

thf('32',plain,
    ( ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ( v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_tops_1 @ X8 @ X9 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X9 @ X8 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('41',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    v2_tops_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['32','38','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k2_pre_topc @ X6 @ ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ X5 @ X7 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X6 ) @ ( k2_pre_topc @ X6 @ X5 ) @ ( k2_pre_topc @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t50_pre_topc])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['10','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TGY3LKppLh
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.24/2.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.24/2.47  % Solved by: fo/fo7.sh
% 2.24/2.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.24/2.47  % done 825 iterations in 2.027s
% 2.24/2.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.24/2.47  % SZS output start Refutation
% 2.24/2.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.24/2.47  thf(sk_C_type, type, sk_C: $i).
% 2.24/2.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.24/2.47  thf(sk_A_type, type, sk_A: $i).
% 2.24/2.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.24/2.47  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 2.24/2.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.24/2.47  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 2.24/2.47  thf(sk_B_type, type, sk_B: $i).
% 2.24/2.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.24/2.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.24/2.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.24/2.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.24/2.47  thf(t90_tops_1, conjecture,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47               ( ( ( v3_tops_1 @ B @ A ) & ( v3_tops_1 @ C @ A ) ) =>
% 2.24/2.47                 ( v3_tops_1 @
% 2.24/2.47                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.24/2.47  thf(zf_stmt_0, negated_conjecture,
% 2.24/2.47    (~( ![A:$i]:
% 2.24/2.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.24/2.47          ( ![B:$i]:
% 2.24/2.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47              ( ![C:$i]:
% 2.24/2.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47                  ( ( ( v3_tops_1 @ B @ A ) & ( v3_tops_1 @ C @ A ) ) =>
% 2.24/2.47                    ( v3_tops_1 @
% 2.24/2.47                      ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 2.24/2.47    inference('cnf.neg', [status(esa)], [t90_tops_1])).
% 2.24/2.47  thf('0', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('1', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(dt_k4_subset_1, axiom,
% 2.24/2.47    (![A:$i,B:$i,C:$i]:
% 2.24/2.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.24/2.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.24/2.47       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.24/2.47  thf('2', plain,
% 2.24/2.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.24/2.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 2.24/2.47          | (m1_subset_1 @ (k4_subset_1 @ X1 @ X0 @ X2) @ (k1_zfmisc_1 @ X1)))),
% 2.24/2.47      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.24/2.47  thf('3', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 2.24/2.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.24/2.47      inference('sup-', [status(thm)], ['1', '2'])).
% 2.24/2.47  thf('4', plain,
% 2.24/2.47      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.24/2.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['0', '3'])).
% 2.24/2.47  thf(d5_tops_1, axiom,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( l1_pre_topc @ A ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47           ( ( v3_tops_1 @ B @ A ) <=>
% 2.24/2.47             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 2.24/2.47  thf('5', plain,
% 2.24/2.47      (![X8 : $i, X9 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.24/2.47          | ~ (v2_tops_1 @ (k2_pre_topc @ X9 @ X8) @ X9)
% 2.24/2.47          | (v3_tops_1 @ X8 @ X9)
% 2.24/2.47          | ~ (l1_pre_topc @ X9))),
% 2.24/2.47      inference('cnf', [status(esa)], [d5_tops_1])).
% 2.24/2.47  thf('6', plain,
% 2.24/2.47      ((~ (l1_pre_topc @ sk_A)
% 2.24/2.47        | (v3_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.24/2.47           sk_A)
% 2.24/2.47        | ~ (v2_tops_1 @ 
% 2.24/2.47             (k2_pre_topc @ sk_A @ 
% 2.24/2.47              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.24/2.47             sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['4', '5'])).
% 2.24/2.47  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('8', plain,
% 2.24/2.47      (((v3_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 2.24/2.47        | ~ (v2_tops_1 @ 
% 2.24/2.47             (k2_pre_topc @ sk_A @ 
% 2.24/2.47              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.24/2.47             sk_A))),
% 2.24/2.47      inference('demod', [status(thm)], ['6', '7'])).
% 2.24/2.47  thf('9', plain,
% 2.24/2.47      (~ (v3_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('10', plain,
% 2.24/2.47      (~ (v2_tops_1 @ 
% 2.24/2.47          (k2_pre_topc @ sk_A @ 
% 2.24/2.47           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.24/2.47          sk_A)),
% 2.24/2.47      inference('clc', [status(thm)], ['8', '9'])).
% 2.24/2.47  thf('11', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(dt_k2_pre_topc, axiom,
% 2.24/2.47    (![A:$i,B:$i]:
% 2.24/2.47     ( ( ( l1_pre_topc @ A ) & 
% 2.24/2.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.24/2.47       ( m1_subset_1 @
% 2.24/2.47         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.24/2.47  thf('12', plain,
% 2.24/2.47      (![X3 : $i, X4 : $i]:
% 2.24/2.47         (~ (l1_pre_topc @ X3)
% 2.24/2.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 2.24/2.47          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 2.24/2.47             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 2.24/2.47      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.24/2.47  thf('13', plain,
% 2.24/2.47      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.24/2.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47        | ~ (l1_pre_topc @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['11', '12'])).
% 2.24/2.47  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('15', plain,
% 2.24/2.47      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 2.24/2.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['13', '14'])).
% 2.24/2.47  thf('16', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('17', plain,
% 2.24/2.47      (![X3 : $i, X4 : $i]:
% 2.24/2.47         (~ (l1_pre_topc @ X3)
% 2.24/2.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 2.24/2.47          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 2.24/2.47             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 2.24/2.47      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.24/2.47  thf('18', plain,
% 2.24/2.47      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.24/2.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47        | ~ (l1_pre_topc @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['16', '17'])).
% 2.24/2.47  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('20', plain,
% 2.24/2.47      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.24/2.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('demod', [status(thm)], ['18', '19'])).
% 2.24/2.47  thf(t85_tops_1, axiom,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47               ( ( ( v2_tops_1 @ B @ A ) & ( v2_tops_1 @ C @ A ) & 
% 2.24/2.47                   ( v4_pre_topc @ C @ A ) ) =>
% 2.24/2.47                 ( v2_tops_1 @
% 2.24/2.47                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.24/2.47  thf('21', plain,
% 2.24/2.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.24/2.47          | ~ (v2_tops_1 @ X12 @ X13)
% 2.24/2.47          | ~ (v2_tops_1 @ X14 @ X13)
% 2.24/2.47          | ~ (v4_pre_topc @ X14 @ X13)
% 2.24/2.47          | (v2_tops_1 @ (k4_subset_1 @ (u1_struct_0 @ X13) @ X12 @ X14) @ X13)
% 2.24/2.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.24/2.47          | ~ (l1_pre_topc @ X13)
% 2.24/2.47          | ~ (v2_pre_topc @ X13))),
% 2.24/2.47      inference('cnf', [status(esa)], [t85_tops_1])).
% 2.24/2.47  thf('22', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (v2_pre_topc @ sk_A)
% 2.24/2.47          | ~ (l1_pre_topc @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | (v2_tops_1 @ 
% 2.24/2.47             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.24/2.47              (k2_pre_topc @ sk_A @ sk_B) @ X0) @ 
% 2.24/2.47             sk_A)
% 2.24/2.47          | ~ (v4_pre_topc @ X0 @ sk_A)
% 2.24/2.47          | ~ (v2_tops_1 @ X0 @ sk_A)
% 2.24/2.47          | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['20', '21'])).
% 2.24/2.47  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('25', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('26', plain,
% 2.24/2.47      (![X8 : $i, X9 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.24/2.47          | ~ (v3_tops_1 @ X8 @ X9)
% 2.24/2.47          | (v2_tops_1 @ (k2_pre_topc @ X9 @ X8) @ X9)
% 2.24/2.47          | ~ (l1_pre_topc @ X9))),
% 2.24/2.47      inference('cnf', [status(esa)], [d5_tops_1])).
% 2.24/2.47  thf('27', plain,
% 2.24/2.47      ((~ (l1_pre_topc @ sk_A)
% 2.24/2.47        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.24/2.47        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['25', '26'])).
% 2.24/2.47  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('29', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('30', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.24/2.47      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.24/2.47  thf('31', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | (v2_tops_1 @ 
% 2.24/2.47             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.24/2.47              (k2_pre_topc @ sk_A @ sk_B) @ X0) @ 
% 2.24/2.47             sk_A)
% 2.24/2.47          | ~ (v4_pre_topc @ X0 @ sk_A)
% 2.24/2.47          | ~ (v2_tops_1 @ X0 @ sk_A))),
% 2.24/2.47      inference('demod', [status(thm)], ['22', '23', '24', '30'])).
% 2.24/2.47  thf('32', plain,
% 2.24/2.47      ((~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)
% 2.24/2.47        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)
% 2.24/2.47        | (v2_tops_1 @ 
% 2.24/2.47           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.24/2.47            (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.24/2.47           sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['15', '31'])).
% 2.24/2.47  thf('33', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('34', plain,
% 2.24/2.47      (![X8 : $i, X9 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 2.24/2.47          | ~ (v3_tops_1 @ X8 @ X9)
% 2.24/2.47          | (v2_tops_1 @ (k2_pre_topc @ X9 @ X8) @ X9)
% 2.24/2.47          | ~ (l1_pre_topc @ X9))),
% 2.24/2.47      inference('cnf', [status(esa)], [d5_tops_1])).
% 2.24/2.47  thf('35', plain,
% 2.24/2.47      ((~ (l1_pre_topc @ sk_A)
% 2.24/2.47        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)
% 2.24/2.47        | ~ (v3_tops_1 @ sk_C @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['33', '34'])).
% 2.24/2.47  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('37', plain, ((v3_tops_1 @ sk_C @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('38', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 2.24/2.47      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.24/2.47  thf('39', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(fc1_tops_1, axiom,
% 2.24/2.47    (![A:$i,B:$i]:
% 2.24/2.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.24/2.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.24/2.47       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 2.24/2.47  thf('40', plain,
% 2.24/2.47      (![X10 : $i, X11 : $i]:
% 2.24/2.47         (~ (l1_pre_topc @ X10)
% 2.24/2.47          | ~ (v2_pre_topc @ X10)
% 2.24/2.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 2.24/2.47          | (v4_pre_topc @ (k2_pre_topc @ X10 @ X11) @ X10))),
% 2.24/2.47      inference('cnf', [status(esa)], [fc1_tops_1])).
% 2.24/2.47  thf('41', plain,
% 2.24/2.47      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)
% 2.24/2.47        | ~ (v2_pre_topc @ sk_A)
% 2.24/2.47        | ~ (l1_pre_topc @ sk_A))),
% 2.24/2.47      inference('sup-', [status(thm)], ['39', '40'])).
% 2.24/2.47  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('44', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 2.24/2.47      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.24/2.47  thf('45', plain,
% 2.24/2.47      ((v2_tops_1 @ 
% 2.24/2.47        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.24/2.47         (k2_pre_topc @ sk_A @ sk_C)) @ 
% 2.24/2.47        sk_A)),
% 2.24/2.47      inference('demod', [status(thm)], ['32', '38', '44'])).
% 2.24/2.47  thf('46', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('47', plain,
% 2.24/2.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf(t50_pre_topc, axiom,
% 2.24/2.47    (![A:$i]:
% 2.24/2.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.24/2.47       ( ![B:$i]:
% 2.24/2.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47           ( ![C:$i]:
% 2.24/2.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.24/2.47               ( ( k2_pre_topc @
% 2.24/2.47                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 2.24/2.47                 ( k4_subset_1 @
% 2.24/2.47                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.24/2.47                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 2.24/2.47  thf('48', plain,
% 2.24/2.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 2.24/2.47          | ((k2_pre_topc @ X6 @ (k4_subset_1 @ (u1_struct_0 @ X6) @ X5 @ X7))
% 2.24/2.47              = (k4_subset_1 @ (u1_struct_0 @ X6) @ (k2_pre_topc @ X6 @ X5) @ 
% 2.24/2.47                 (k2_pre_topc @ X6 @ X7)))
% 2.24/2.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 2.24/2.47          | ~ (l1_pre_topc @ X6)
% 2.24/2.47          | ~ (v2_pre_topc @ X6))),
% 2.24/2.47      inference('cnf', [status(esa)], [t50_pre_topc])).
% 2.24/2.47  thf('49', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (v2_pre_topc @ sk_A)
% 2.24/2.47          | ~ (l1_pre_topc @ sk_A)
% 2.24/2.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | ((k2_pre_topc @ sk_A @ 
% 2.24/2.47              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 2.24/2.47              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.24/2.47                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.24/2.47      inference('sup-', [status(thm)], ['47', '48'])).
% 2.24/2.47  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 2.24/2.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.24/2.47  thf('52', plain,
% 2.24/2.47      (![X0 : $i]:
% 2.24/2.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.24/2.47          | ((k2_pre_topc @ sk_A @ 
% 2.24/2.47              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 2.24/2.47              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.24/2.47                 (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 2.24/2.47      inference('demod', [status(thm)], ['49', '50', '51'])).
% 2.24/2.47  thf('53', plain,
% 2.24/2.47      (((k2_pre_topc @ sk_A @ 
% 2.24/2.47         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 2.24/2.47         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.24/2.47            (k2_pre_topc @ sk_A @ sk_C)))),
% 2.24/2.47      inference('sup-', [status(thm)], ['46', '52'])).
% 2.24/2.47  thf('54', plain,
% 2.24/2.47      ((v2_tops_1 @ 
% 2.24/2.47        (k2_pre_topc @ sk_A @ 
% 2.24/2.47         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 2.24/2.47        sk_A)),
% 2.24/2.47      inference('demod', [status(thm)], ['45', '53'])).
% 2.24/2.47  thf('55', plain, ($false), inference('demod', [status(thm)], ['10', '54'])).
% 2.24/2.47  
% 2.24/2.47  % SZS output end Refutation
% 2.24/2.47  
% 2.24/2.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
