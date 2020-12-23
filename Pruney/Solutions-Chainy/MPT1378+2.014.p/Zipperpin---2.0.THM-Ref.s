%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uENuTpQjVA

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:47 EST 2020

% Result     : Theorem 3.90s
% Output     : Refutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 163 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  791 (2655 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_connsp_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_connsp_2 @ X27 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ X0 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('34',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ( m1_connsp_2 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['59','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uENuTpQjVA
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.90/4.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.90/4.14  % Solved by: fo/fo7.sh
% 3.90/4.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.90/4.14  % done 3736 iterations in 3.698s
% 3.90/4.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.90/4.14  % SZS output start Refutation
% 3.90/4.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.90/4.14  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.90/4.14  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.90/4.14  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 3.90/4.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.90/4.14  thf(sk_B_type, type, sk_B: $i).
% 3.90/4.14  thf(sk_A_type, type, sk_A: $i).
% 3.90/4.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.90/4.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.90/4.14  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.90/4.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.90/4.14  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.90/4.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.90/4.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.90/4.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.90/4.14  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.90/4.14  thf(sk_D_type, type, sk_D: $i).
% 3.90/4.14  thf(t3_connsp_2, conjecture,
% 3.90/4.14    (![A:$i]:
% 3.90/4.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.90/4.14       ( ![B:$i]:
% 3.90/4.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.90/4.14           ( ![C:$i]:
% 3.90/4.14             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14               ( ![D:$i]:
% 3.90/4.14                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 3.90/4.14                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 3.90/4.14                     ( m1_connsp_2 @
% 3.90/4.14                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 3.90/4.14  thf(zf_stmt_0, negated_conjecture,
% 3.90/4.14    (~( ![A:$i]:
% 3.90/4.14        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.90/4.14            ( l1_pre_topc @ A ) ) =>
% 3.90/4.14          ( ![B:$i]:
% 3.90/4.14            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.90/4.14              ( ![C:$i]:
% 3.90/4.14                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14                  ( ![D:$i]:
% 3.90/4.14                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 3.90/4.14                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 3.90/4.14                        ( m1_connsp_2 @
% 3.90/4.14                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 3.90/4.14    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 3.90/4.14  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('1', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('2', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf(d1_connsp_2, axiom,
% 3.90/4.14    (![A:$i]:
% 3.90/4.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.90/4.14       ( ![B:$i]:
% 3.90/4.14         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.90/4.14           ( ![C:$i]:
% 3.90/4.14             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 3.90/4.14                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.90/4.14  thf('3', plain,
% 3.90/4.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.90/4.14         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.90/4.14          | ~ (m1_connsp_2 @ X27 @ X26 @ X25)
% 3.90/4.14          | (r2_hidden @ X25 @ (k1_tops_1 @ X26 @ X27))
% 3.90/4.14          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.90/4.14          | ~ (l1_pre_topc @ X26)
% 3.90/4.14          | ~ (v2_pre_topc @ X26)
% 3.90/4.14          | (v2_struct_0 @ X26))),
% 3.90/4.14      inference('cnf', [status(esa)], [d1_connsp_2])).
% 3.90/4.14  thf('4', plain,
% 3.90/4.14      (![X0 : $i]:
% 3.90/4.14         ((v2_struct_0 @ sk_A)
% 3.90/4.14          | ~ (v2_pre_topc @ sk_A)
% 3.90/4.14          | ~ (l1_pre_topc @ sk_A)
% 3.90/4.14          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 3.90/4.14          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 3.90/4.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('sup-', [status(thm)], ['2', '3'])).
% 3.90/4.14  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('7', plain,
% 3.90/4.14      (![X0 : $i]:
% 3.90/4.14         ((v2_struct_0 @ sk_A)
% 3.90/4.14          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 3.90/4.14          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 3.90/4.14          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('demod', [status(thm)], ['4', '5', '6'])).
% 3.90/4.14  thf('8', plain,
% 3.90/4.14      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.90/4.14        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))
% 3.90/4.14        | (v2_struct_0 @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['1', '7'])).
% 3.90/4.14  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('10', plain,
% 3.90/4.14      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A))),
% 3.90/4.14      inference('demod', [status(thm)], ['8', '9'])).
% 3.90/4.14  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))),
% 3.90/4.14      inference('clc', [status(thm)], ['10', '11'])).
% 3.90/4.14  thf('13', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf(t3_subset, axiom,
% 3.90/4.14    (![A:$i,B:$i]:
% 3.90/4.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.90/4.14  thf('14', plain,
% 3.90/4.14      (![X13 : $i, X14 : $i]:
% 3.90/4.14         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.90/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.90/4.14  thf('15', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['13', '14'])).
% 3.90/4.14  thf('16', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('17', plain,
% 3.90/4.14      (![X13 : $i, X14 : $i]:
% 3.90/4.14         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 3.90/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.90/4.14  thf('18', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['16', '17'])).
% 3.90/4.14  thf(t8_xboole_1, axiom,
% 3.90/4.14    (![A:$i,B:$i,C:$i]:
% 3.90/4.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.90/4.14       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.90/4.14  thf('19', plain,
% 3.90/4.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.90/4.14         (~ (r1_tarski @ X7 @ X8)
% 3.90/4.14          | ~ (r1_tarski @ X9 @ X8)
% 3.90/4.14          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 3.90/4.14      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.90/4.14  thf('20', plain,
% 3.90/4.14      (![X0 : $i]:
% 3.90/4.14         ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 3.90/4.14          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('sup-', [status(thm)], ['18', '19'])).
% 3.90/4.14  thf('21', plain,
% 3.90/4.14      ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['15', '20'])).
% 3.90/4.14  thf('22', plain,
% 3.90/4.14      (![X13 : $i, X15 : $i]:
% 3.90/4.14         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 3.90/4.14      inference('cnf', [status(esa)], [t3_subset])).
% 3.90/4.14  thf('23', plain,
% 3.90/4.14      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 3.90/4.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('sup-', [status(thm)], ['21', '22'])).
% 3.90/4.14  thf('24', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf(dt_k1_tops_1, axiom,
% 3.90/4.14    (![A:$i,B:$i]:
% 3.90/4.14     ( ( ( l1_pre_topc @ A ) & 
% 3.90/4.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.90/4.14       ( m1_subset_1 @
% 3.90/4.14         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.90/4.14  thf('25', plain,
% 3.90/4.14      (![X16 : $i, X17 : $i]:
% 3.90/4.14         (~ (l1_pre_topc @ X16)
% 3.90/4.14          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 3.90/4.14          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 3.90/4.14             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 3.90/4.14      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.90/4.14  thf('26', plain,
% 3.90/4.14      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.90/4.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.90/4.14        | ~ (l1_pre_topc @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['24', '25'])).
% 3.90/4.14  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('28', plain,
% 3.90/4.14      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.90/4.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('demod', [status(thm)], ['26', '27'])).
% 3.90/4.14  thf(t56_tops_1, axiom,
% 3.90/4.14    (![A:$i]:
% 3.90/4.14     ( ( l1_pre_topc @ A ) =>
% 3.90/4.14       ( ![B:$i]:
% 3.90/4.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14           ( ![C:$i]:
% 3.90/4.14             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.90/4.14                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.90/4.14  thf('29', plain,
% 3.90/4.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.90/4.14         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 3.90/4.14          | ~ (v3_pre_topc @ X22 @ X23)
% 3.90/4.14          | ~ (r1_tarski @ X22 @ X24)
% 3.90/4.14          | (r1_tarski @ X22 @ (k1_tops_1 @ X23 @ X24))
% 3.90/4.14          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 3.90/4.14          | ~ (l1_pre_topc @ X23))),
% 3.90/4.14      inference('cnf', [status(esa)], [t56_tops_1])).
% 3.90/4.14  thf('30', plain,
% 3.90/4.14      (![X0 : $i]:
% 3.90/4.14         (~ (l1_pre_topc @ sk_A)
% 3.90/4.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.90/4.14          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 3.90/4.14          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ X0)
% 3.90/4.14          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_D) @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['28', '29'])).
% 3.90/4.14  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('32', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf(fc9_tops_1, axiom,
% 3.90/4.14    (![A:$i,B:$i]:
% 3.90/4.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.90/4.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.90/4.14       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 3.90/4.14  thf('33', plain,
% 3.90/4.14      (![X18 : $i, X19 : $i]:
% 3.90/4.14         (~ (l1_pre_topc @ X18)
% 3.90/4.14          | ~ (v2_pre_topc @ X18)
% 3.90/4.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.90/4.14          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 3.90/4.14      inference('cnf', [status(esa)], [fc9_tops_1])).
% 3.90/4.14  thf('34', plain,
% 3.90/4.14      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_D) @ sk_A)
% 3.90/4.14        | ~ (v2_pre_topc @ sk_A)
% 3.90/4.14        | ~ (l1_pre_topc @ sk_A))),
% 3.90/4.14      inference('sup-', [status(thm)], ['32', '33'])).
% 3.90/4.14  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('37', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_D) @ sk_A)),
% 3.90/4.14      inference('demod', [status(thm)], ['34', '35', '36'])).
% 3.90/4.14  thf('38', plain,
% 3.90/4.14      (![X0 : $i]:
% 3.90/4.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.90/4.14          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 3.90/4.14          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ X0))),
% 3.90/4.14      inference('demod', [status(thm)], ['30', '31', '37'])).
% 3.90/4.14  thf('39', plain,
% 3.90/4.14      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.90/4.14           (k2_xboole_0 @ sk_C_1 @ sk_D))
% 3.90/4.14        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.90/4.14           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D))))),
% 3.90/4.14      inference('sup-', [status(thm)], ['23', '38'])).
% 3.90/4.14  thf('40', plain,
% 3.90/4.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf(t44_tops_1, axiom,
% 3.90/4.14    (![A:$i]:
% 3.90/4.14     ( ( l1_pre_topc @ A ) =>
% 3.90/4.14       ( ![B:$i]:
% 3.90/4.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.14           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 3.90/4.14  thf('41', plain,
% 3.90/4.14      (![X20 : $i, X21 : $i]:
% 3.90/4.14         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 3.90/4.14          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 3.90/4.14          | ~ (l1_pre_topc @ X21))),
% 3.90/4.14      inference('cnf', [status(esa)], [t44_tops_1])).
% 3.90/4.14  thf('42', plain,
% 3.90/4.14      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D))),
% 3.90/4.14      inference('sup-', [status(thm)], ['40', '41'])).
% 3.90/4.14  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.14  thf('44', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)),
% 3.90/4.14      inference('demod', [status(thm)], ['42', '43'])).
% 3.98/4.14  thf(t10_xboole_1, axiom,
% 3.98/4.14    (![A:$i,B:$i,C:$i]:
% 3.98/4.14     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.98/4.14  thf('45', plain,
% 3.98/4.14      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.98/4.14         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 3.98/4.14      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.98/4.14  thf('46', plain,
% 3.98/4.14      (![X0 : $i]:
% 3.98/4.14         (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k2_xboole_0 @ X0 @ sk_D))),
% 3.98/4.14      inference('sup-', [status(thm)], ['44', '45'])).
% 3.98/4.14  thf('47', plain,
% 3.98/4.14      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 3.98/4.14        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 3.98/4.14      inference('demod', [status(thm)], ['39', '46'])).
% 3.98/4.14  thf(d3_tarski, axiom,
% 3.98/4.14    (![A:$i,B:$i]:
% 3.98/4.14     ( ( r1_tarski @ A @ B ) <=>
% 3.98/4.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.98/4.14  thf('48', plain,
% 3.98/4.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.98/4.14         (~ (r2_hidden @ X0 @ X1)
% 3.98/4.14          | (r2_hidden @ X0 @ X2)
% 3.98/4.14          | ~ (r1_tarski @ X1 @ X2))),
% 3.98/4.14      inference('cnf', [status(esa)], [d3_tarski])).
% 3.98/4.14  thf('49', plain,
% 3.98/4.15      (![X0 : $i]:
% 3.98/4.15         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.98/4.15          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 3.98/4.15      inference('sup-', [status(thm)], ['47', '48'])).
% 3.98/4.15  thf('50', plain,
% 3.98/4.15      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))),
% 3.98/4.15      inference('sup-', [status(thm)], ['12', '49'])).
% 3.98/4.15  thf('51', plain,
% 3.98/4.15      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ 
% 3.98/4.15        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.98/4.15      inference('sup-', [status(thm)], ['21', '22'])).
% 3.98/4.15  thf('52', plain,
% 3.98/4.15      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.98/4.15         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.98/4.15          | ~ (r2_hidden @ X25 @ (k1_tops_1 @ X26 @ X27))
% 3.98/4.15          | (m1_connsp_2 @ X27 @ X26 @ X25)
% 3.98/4.15          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.98/4.15          | ~ (l1_pre_topc @ X26)
% 3.98/4.15          | ~ (v2_pre_topc @ X26)
% 3.98/4.15          | (v2_struct_0 @ X26))),
% 3.98/4.15      inference('cnf', [status(esa)], [d1_connsp_2])).
% 3.98/4.15  thf('53', plain,
% 3.98/4.15      (![X0 : $i]:
% 3.98/4.15         ((v2_struct_0 @ sk_A)
% 3.98/4.15          | ~ (v2_pre_topc @ sk_A)
% 3.98/4.15          | ~ (l1_pre_topc @ sk_A)
% 3.98/4.15          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 3.98/4.15          | ~ (r2_hidden @ X0 @ 
% 3.98/4.15               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.98/4.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.98/4.15      inference('sup-', [status(thm)], ['51', '52'])).
% 3.98/4.15  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf('56', plain,
% 3.98/4.15      (![X0 : $i]:
% 3.98/4.15         ((v2_struct_0 @ sk_A)
% 3.98/4.15          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ X0)
% 3.98/4.15          | ~ (r2_hidden @ X0 @ 
% 3.98/4.15               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D)))
% 3.98/4.15          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.98/4.15      inference('demod', [status(thm)], ['53', '54', '55'])).
% 3.98/4.15  thf('57', plain,
% 3.98/4.15      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.98/4.15        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 3.98/4.15        | (v2_struct_0 @ sk_A))),
% 3.98/4.15      inference('sup-', [status(thm)], ['50', '56'])).
% 3.98/4.15  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf('59', plain,
% 3.98/4.15      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)
% 3.98/4.15        | (v2_struct_0 @ sk_A))),
% 3.98/4.15      inference('demod', [status(thm)], ['57', '58'])).
% 3.98/4.15  thf('60', plain,
% 3.98/4.15      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D) @ 
% 3.98/4.15          sk_A @ sk_B)),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf('61', plain,
% 3.98/4.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf('62', plain,
% 3.98/4.15      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.98/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.98/4.15  thf(redefinition_k4_subset_1, axiom,
% 3.98/4.15    (![A:$i,B:$i,C:$i]:
% 3.98/4.15     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.98/4.15         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.98/4.15       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.98/4.15  thf('63', plain,
% 3.98/4.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.98/4.15         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.98/4.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 3.98/4.15          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 3.98/4.15      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.98/4.15  thf('64', plain,
% 3.98/4.15      (![X0 : $i]:
% 3.98/4.15         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 3.98/4.15            = (k2_xboole_0 @ sk_C_1 @ X0))
% 3.98/4.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.98/4.15      inference('sup-', [status(thm)], ['62', '63'])).
% 3.98/4.15  thf('65', plain,
% 3.98/4.15      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D)
% 3.98/4.15         = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 3.98/4.15      inference('sup-', [status(thm)], ['61', '64'])).
% 3.98/4.15  thf('66', plain,
% 3.98/4.15      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D) @ sk_A @ sk_B)),
% 3.98/4.15      inference('demod', [status(thm)], ['60', '65'])).
% 3.98/4.15  thf('67', plain, ((v2_struct_0 @ sk_A)),
% 3.98/4.15      inference('clc', [status(thm)], ['59', '66'])).
% 3.98/4.15  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 3.98/4.15  
% 3.98/4.15  % SZS output end Refutation
% 3.98/4.15  
% 3.98/4.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
