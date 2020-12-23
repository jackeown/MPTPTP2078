%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eKqO0902Fv

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:45 EST 2020

% Result     : Theorem 11.93s
% Output     : Refutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 224 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  949 (4235 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t3_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                   => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                     => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X19 )
      | ~ ( v3_pre_topc @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X20 @ X19 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_tops_1 @ X14 @ ( k1_tops_1 @ X14 @ X15 ) )
        = ( k1_tops_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39','40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('50',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','53','58'])).

thf('60',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('72',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['69','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eKqO0902Fv
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.93/12.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.93/12.15  % Solved by: fo/fo7.sh
% 11.93/12.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.93/12.15  % done 5030 iterations in 11.648s
% 11.93/12.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.93/12.15  % SZS output start Refutation
% 11.93/12.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.93/12.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.93/12.15  thf(sk_A_type, type, sk_A: $i).
% 11.93/12.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 11.93/12.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.93/12.15  thf(sk_B_type, type, sk_B: $i).
% 11.93/12.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.93/12.15  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 11.93/12.15  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 11.93/12.15  thf(sk_D_1_type, type, sk_D_1: $i).
% 11.93/12.15  thf(sk_C_type, type, sk_C: $i).
% 11.93/12.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.93/12.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.93/12.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.93/12.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.93/12.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.93/12.15  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 11.93/12.15  thf(t3_connsp_2, conjecture,
% 11.93/12.15    (![A:$i]:
% 11.93/12.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.93/12.15       ( ![B:$i]:
% 11.93/12.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.93/12.15           ( ![C:$i]:
% 11.93/12.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15               ( ![D:$i]:
% 11.93/12.15                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 11.93/12.15                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 11.93/12.15                     ( m1_connsp_2 @
% 11.93/12.15                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 11.93/12.15  thf(zf_stmt_0, negated_conjecture,
% 11.93/12.15    (~( ![A:$i]:
% 11.93/12.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 11.93/12.15            ( l1_pre_topc @ A ) ) =>
% 11.93/12.15          ( ![B:$i]:
% 11.93/12.15            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.93/12.15              ( ![C:$i]:
% 11.93/12.15                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15                  ( ![D:$i]:
% 11.93/12.15                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 11.93/12.15                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 11.93/12.15                        ( m1_connsp_2 @
% 11.93/12.15                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 11.93/12.15    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 11.93/12.15  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('1', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('2', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf(d1_connsp_2, axiom,
% 11.93/12.15    (![A:$i]:
% 11.93/12.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.93/12.15       ( ![B:$i]:
% 11.93/12.15         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.93/12.15           ( ![C:$i]:
% 11.93/12.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 11.93/12.15                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 11.93/12.15  thf('3', plain,
% 11.93/12.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 11.93/12.15          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 11.93/12.15          | (r2_hidden @ X23 @ (k1_tops_1 @ X24 @ X25))
% 11.93/12.15          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 11.93/12.15          | ~ (l1_pre_topc @ X24)
% 11.93/12.15          | ~ (v2_pre_topc @ X24)
% 11.93/12.15          | (v2_struct_0 @ X24))),
% 11.93/12.15      inference('cnf', [status(esa)], [d1_connsp_2])).
% 11.93/12.15  thf('4', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         ((v2_struct_0 @ sk_A)
% 11.93/12.15          | ~ (v2_pre_topc @ sk_A)
% 11.93/12.15          | ~ (l1_pre_topc @ sk_A)
% 11.93/12.15          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 11.93/12.15          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 11.93/12.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('sup-', [status(thm)], ['2', '3'])).
% 11.93/12.15  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('7', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         ((v2_struct_0 @ sk_A)
% 11.93/12.15          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 11.93/12.15          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 11.93/12.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('demod', [status(thm)], ['4', '5', '6'])).
% 11.93/12.15  thf('8', plain,
% 11.93/12.15      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 11.93/12.15        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 11.93/12.15        | (v2_struct_0 @ sk_A))),
% 11.93/12.15      inference('sup-', [status(thm)], ['1', '7'])).
% 11.93/12.15  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('10', plain,
% 11.93/12.15      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 11.93/12.15      inference('demod', [status(thm)], ['8', '9'])).
% 11.93/12.15  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 11.93/12.15      inference('clc', [status(thm)], ['10', '11'])).
% 11.93/12.15  thf('13', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('14', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf(dt_k4_subset_1, axiom,
% 11.93/12.15    (![A:$i,B:$i,C:$i]:
% 11.93/12.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 11.93/12.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 11.93/12.15       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 11.93/12.15  thf('15', plain,
% 11.93/12.15      (![X4 : $i, X5 : $i, X6 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 11.93/12.15          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5))
% 11.93/12.15          | (m1_subset_1 @ (k4_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 11.93/12.15      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 11.93/12.15  thf('16', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 11.93/12.15           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.93/12.15      inference('sup-', [status(thm)], ['14', '15'])).
% 11.93/12.15  thf('17', plain,
% 11.93/12.15      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 11.93/12.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('sup-', [status(thm)], ['13', '16'])).
% 11.93/12.15  thf('18', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('19', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf(redefinition_k4_subset_1, axiom,
% 11.93/12.15    (![A:$i,B:$i,C:$i]:
% 11.93/12.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 11.93/12.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 11.93/12.15       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 11.93/12.15  thf('20', plain,
% 11.93/12.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 11.93/12.15          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 11.93/12.15          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 11.93/12.15      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 11.93/12.15  thf('21', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 11.93/12.15            = (k2_xboole_0 @ sk_C @ X0))
% 11.93/12.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 11.93/12.15      inference('sup-', [status(thm)], ['19', '20'])).
% 11.93/12.15  thf('22', plain,
% 11.93/12.15      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 11.93/12.15         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 11.93/12.15      inference('sup-', [status(thm)], ['18', '21'])).
% 11.93/12.15  thf('23', plain,
% 11.93/12.15      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 11.93/12.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('demod', [status(thm)], ['17', '22'])).
% 11.93/12.15  thf('24', plain,
% 11.93/12.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf(t48_tops_1, axiom,
% 11.93/12.15    (![A:$i]:
% 11.93/12.15     ( ( l1_pre_topc @ A ) =>
% 11.93/12.15       ( ![B:$i]:
% 11.93/12.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15           ( ![C:$i]:
% 11.93/12.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15               ( ( r1_tarski @ B @ C ) =>
% 11.93/12.15                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 11.93/12.15  thf('25', plain,
% 11.93/12.15      (![X16 : $i, X17 : $i, X18 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 11.93/12.15          | ~ (r1_tarski @ X16 @ X18)
% 11.93/12.15          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ (k1_tops_1 @ X17 @ X18))
% 11.93/12.15          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 11.93/12.15          | ~ (l1_pre_topc @ X17))),
% 11.93/12.15      inference('cnf', [status(esa)], [t48_tops_1])).
% 11.93/12.15  thf('26', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         (~ (l1_pre_topc @ sk_A)
% 11.93/12.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.15          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 11.93/12.15          | ~ (r1_tarski @ sk_C @ X0))),
% 11.93/12.15      inference('sup-', [status(thm)], ['24', '25'])).
% 11.93/12.15  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('28', plain,
% 11.93/12.15      (![X0 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.15          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 11.93/12.15          | ~ (r1_tarski @ sk_C @ X0))),
% 11.93/12.15      inference('demod', [status(thm)], ['26', '27'])).
% 11.93/12.15  thf('29', plain,
% 11.93/12.15      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 11.93/12.15        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 11.93/12.15           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 11.93/12.15      inference('sup-', [status(thm)], ['23', '28'])).
% 11.93/12.15  thf(t7_xboole_1, axiom,
% 11.93/12.15    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 11.93/12.15  thf('30', plain,
% 11.93/12.15      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 11.93/12.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 11.93/12.15  thf('31', plain,
% 11.93/12.15      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 11.93/12.15        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 11.93/12.15      inference('demod', [status(thm)], ['29', '30'])).
% 11.93/12.15  thf('32', plain,
% 11.93/12.15      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 11.93/12.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('demod', [status(thm)], ['17', '22'])).
% 11.93/12.15  thf(dt_k1_tops_1, axiom,
% 11.93/12.15    (![A:$i,B:$i]:
% 11.93/12.15     ( ( ( l1_pre_topc @ A ) & 
% 11.93/12.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.93/12.15       ( m1_subset_1 @
% 11.93/12.15         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 11.93/12.15  thf('33', plain,
% 11.93/12.15      (![X10 : $i, X11 : $i]:
% 11.93/12.15         (~ (l1_pre_topc @ X10)
% 11.93/12.15          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 11.93/12.15          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 11.93/12.15             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 11.93/12.15      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 11.93/12.15  thf('34', plain,
% 11.93/12.15      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)) @ 
% 11.93/12.15         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.15        | ~ (l1_pre_topc @ sk_A))),
% 11.93/12.15      inference('sup-', [status(thm)], ['32', '33'])).
% 11.93/12.15  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.15  thf('36', plain,
% 11.93/12.15      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)) @ 
% 11.93/12.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.15      inference('demod', [status(thm)], ['34', '35'])).
% 11.93/12.15  thf(t54_tops_1, axiom,
% 11.93/12.15    (![A:$i]:
% 11.93/12.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.93/12.15       ( ![B:$i,C:$i]:
% 11.93/12.15         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.93/12.15           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 11.93/12.15             ( ?[D:$i]:
% 11.93/12.15               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 11.93/12.15                 ( v3_pre_topc @ D @ A ) & 
% 11.93/12.15                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 11.93/12.15  thf('37', plain,
% 11.93/12.15      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 11.93/12.15         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 11.93/12.15          | ~ (r2_hidden @ X21 @ X22)
% 11.93/12.15          | ~ (r1_tarski @ X22 @ X19)
% 11.93/12.15          | ~ (v3_pre_topc @ X22 @ X20)
% 11.93/12.15          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 11.93/12.15          | (r2_hidden @ X21 @ (k1_tops_1 @ X20 @ X19))
% 11.93/12.15          | ~ (l1_pre_topc @ X20)
% 11.93/12.15          | ~ (v2_pre_topc @ X20))),
% 11.93/12.15      inference('cnf', [status(esa)], [t54_tops_1])).
% 11.93/12.15  thf('38', plain,
% 11.93/12.15      (![X0 : $i, X1 : $i]:
% 11.93/12.15         (~ (v2_pre_topc @ sk_A)
% 11.93/12.15          | ~ (l1_pre_topc @ sk_A)
% 11.93/12.16          | (r2_hidden @ X0 @ 
% 11.93/12.16             (k1_tops_1 @ sk_A @ 
% 11.93/12.16              (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))
% 11.93/12.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.16          | ~ (v3_pre_topc @ X1 @ sk_A)
% 11.93/12.16          | ~ (r1_tarski @ X1 @ 
% 11.93/12.16               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          | ~ (r2_hidden @ X0 @ X1))),
% 11.93/12.16      inference('sup-', [status(thm)], ['36', '37'])).
% 11.93/12.16  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('41', plain,
% 11.93/12.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 11.93/12.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('demod', [status(thm)], ['17', '22'])).
% 11.93/12.16  thf(projectivity_k1_tops_1, axiom,
% 11.93/12.16    (![A:$i,B:$i]:
% 11.93/12.16     ( ( ( l1_pre_topc @ A ) & 
% 11.93/12.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.93/12.16       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 11.93/12.16  thf('42', plain,
% 11.93/12.16      (![X14 : $i, X15 : $i]:
% 11.93/12.16         (~ (l1_pre_topc @ X14)
% 11.93/12.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 11.93/12.16          | ((k1_tops_1 @ X14 @ (k1_tops_1 @ X14 @ X15))
% 11.93/12.16              = (k1_tops_1 @ X14 @ X15)))),
% 11.93/12.16      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 11.93/12.16  thf('43', plain,
% 11.93/12.16      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          = (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16        | ~ (l1_pre_topc @ sk_A))),
% 11.93/12.16      inference('sup-', [status(thm)], ['41', '42'])).
% 11.93/12.16  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('45', plain,
% 11.93/12.16      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16         = (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 11.93/12.16      inference('demod', [status(thm)], ['43', '44'])).
% 11.93/12.16  thf('46', plain,
% 11.93/12.16      (![X0 : $i, X1 : $i]:
% 11.93/12.16         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.16          | ~ (v3_pre_topc @ X1 @ sk_A)
% 11.93/12.16          | ~ (r1_tarski @ X1 @ 
% 11.93/12.16               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          | ~ (r2_hidden @ X0 @ X1))),
% 11.93/12.16      inference('demod', [status(thm)], ['38', '39', '40', '45'])).
% 11.93/12.16  thf('47', plain,
% 11.93/12.16      (![X0 : $i]:
% 11.93/12.16         (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 11.93/12.16          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 11.93/12.16          | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 11.93/12.16               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.16          | (r2_hidden @ X0 @ 
% 11.93/12.16             (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 11.93/12.16      inference('sup-', [status(thm)], ['31', '46'])).
% 11.93/12.16  thf('48', plain,
% 11.93/12.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf(fc9_tops_1, axiom,
% 11.93/12.16    (![A:$i,B:$i]:
% 11.93/12.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 11.93/12.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 11.93/12.16       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 11.93/12.16  thf('49', plain,
% 11.93/12.16      (![X12 : $i, X13 : $i]:
% 11.93/12.16         (~ (l1_pre_topc @ X12)
% 11.93/12.16          | ~ (v2_pre_topc @ X12)
% 11.93/12.16          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 11.93/12.16          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 11.93/12.16      inference('cnf', [status(esa)], [fc9_tops_1])).
% 11.93/12.16  thf('50', plain,
% 11.93/12.16      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 11.93/12.16        | ~ (v2_pre_topc @ sk_A)
% 11.93/12.16        | ~ (l1_pre_topc @ sk_A))),
% 11.93/12.16      inference('sup-', [status(thm)], ['48', '49'])).
% 11.93/12.16  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('53', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 11.93/12.16      inference('demod', [status(thm)], ['50', '51', '52'])).
% 11.93/12.16  thf('54', plain,
% 11.93/12.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('55', plain,
% 11.93/12.16      (![X10 : $i, X11 : $i]:
% 11.93/12.16         (~ (l1_pre_topc @ X10)
% 11.93/12.16          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 11.93/12.16          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 11.93/12.16             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 11.93/12.16      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 11.93/12.16  thf('56', plain,
% 11.93/12.16      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 11.93/12.16         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.93/12.16        | ~ (l1_pre_topc @ sk_A))),
% 11.93/12.16      inference('sup-', [status(thm)], ['54', '55'])).
% 11.93/12.16  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('58', plain,
% 11.93/12.16      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 11.93/12.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('demod', [status(thm)], ['56', '57'])).
% 11.93/12.16  thf('59', plain,
% 11.93/12.16      (![X0 : $i]:
% 11.93/12.16         (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 11.93/12.16          | (r2_hidden @ X0 @ 
% 11.93/12.16             (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 11.93/12.16      inference('demod', [status(thm)], ['47', '53', '58'])).
% 11.93/12.16  thf('60', plain,
% 11.93/12.16      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 11.93/12.16      inference('sup-', [status(thm)], ['12', '59'])).
% 11.93/12.16  thf('61', plain,
% 11.93/12.16      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 11.93/12.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('demod', [status(thm)], ['17', '22'])).
% 11.93/12.16  thf('62', plain,
% 11.93/12.16      (![X23 : $i, X24 : $i, X25 : $i]:
% 11.93/12.16         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 11.93/12.16          | ~ (r2_hidden @ X23 @ (k1_tops_1 @ X24 @ X25))
% 11.93/12.16          | (m1_connsp_2 @ X25 @ X24 @ X23)
% 11.93/12.16          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 11.93/12.16          | ~ (l1_pre_topc @ X24)
% 11.93/12.16          | ~ (v2_pre_topc @ X24)
% 11.93/12.16          | (v2_struct_0 @ X24))),
% 11.93/12.16      inference('cnf', [status(esa)], [d1_connsp_2])).
% 11.93/12.16  thf('63', plain,
% 11.93/12.16      (![X0 : $i]:
% 11.93/12.16         ((v2_struct_0 @ sk_A)
% 11.93/12.16          | ~ (v2_pre_topc @ sk_A)
% 11.93/12.16          | ~ (l1_pre_topc @ sk_A)
% 11.93/12.16          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 11.93/12.16          | ~ (r2_hidden @ X0 @ 
% 11.93/12.16               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('sup-', [status(thm)], ['61', '62'])).
% 11.93/12.16  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('66', plain,
% 11.93/12.16      (![X0 : $i]:
% 11.93/12.16         ((v2_struct_0 @ sk_A)
% 11.93/12.16          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 11.93/12.16          | ~ (r2_hidden @ X0 @ 
% 11.93/12.16               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 11.93/12.16          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.93/12.16      inference('demod', [status(thm)], ['63', '64', '65'])).
% 11.93/12.16  thf('67', plain,
% 11.93/12.16      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 11.93/12.16        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 11.93/12.16        | (v2_struct_0 @ sk_A))),
% 11.93/12.16      inference('sup-', [status(thm)], ['60', '66'])).
% 11.93/12.16  thf('68', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('69', plain,
% 11.93/12.16      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 11.93/12.16        | (v2_struct_0 @ sk_A))),
% 11.93/12.16      inference('demod', [status(thm)], ['67', '68'])).
% 11.93/12.16  thf('70', plain,
% 11.93/12.16      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 11.93/12.16          sk_A @ sk_B)),
% 11.93/12.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.93/12.16  thf('71', plain,
% 11.93/12.16      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 11.93/12.16         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 11.93/12.16      inference('sup-', [status(thm)], ['18', '21'])).
% 11.93/12.16  thf('72', plain,
% 11.93/12.16      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)),
% 11.93/12.16      inference('demod', [status(thm)], ['70', '71'])).
% 11.93/12.16  thf('73', plain, ((v2_struct_0 @ sk_A)),
% 11.93/12.16      inference('clc', [status(thm)], ['69', '72'])).
% 11.93/12.16  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 11.93/12.16  
% 11.93/12.16  % SZS output end Refutation
% 11.93/12.16  
% 11.93/12.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
