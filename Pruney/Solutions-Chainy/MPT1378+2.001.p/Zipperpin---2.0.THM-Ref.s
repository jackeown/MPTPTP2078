%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVWJhSy0Qp

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:45 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 210 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  741 (3781 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('53',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['50','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','56'])).

thf('58',plain,(
    $false ),
    inference('sup-',[status(thm)],['11','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVWJhSy0Qp
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 1144 iterations in 0.481s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.75/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.94  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.75/0.94  thf(t3_connsp_2, conjecture,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94               ( ![D:$i]:
% 0.75/0.94                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.75/0.94                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.75/0.94                     ( m1_connsp_2 @
% 0.75/0.94                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i]:
% 0.75/0.94        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.94            ( l1_pre_topc @ A ) ) =>
% 0.75/0.94          ( ![B:$i]:
% 0.75/0.94            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.94              ( ![C:$i]:
% 0.75/0.94                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94                  ( ![D:$i]:
% 0.75/0.94                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.75/0.94                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.75/0.94                        ( m1_connsp_2 @
% 0.75/0.94                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.75/0.94  thf('0', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(d1_connsp_2, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.75/0.94                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.75/0.94          | ~ (m1_connsp_2 @ X28 @ X27 @ X26)
% 0.75/0.94          | (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 0.75/0.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.75/0.94          | ~ (l1_pre_topc @ X27)
% 0.75/0.94          | ~ (v2_pre_topc @ X27)
% 0.75/0.94          | (v2_struct_0 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v2_struct_0 @ sk_A)
% 0.75/0.94          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.94          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.94          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.75/0.94          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.94  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v2_struct_0 @ sk_A)
% 0.75/0.94          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.75/0.94          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.75/0.94        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.75/0.94        | (v2_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '6'])).
% 0.75/0.94  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '8'])).
% 0.75/0.94  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.75/0.94      inference('clc', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(dt_k4_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.94       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.75/0.94          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.75/0.94          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.75/0.94      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.75/0.94           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['12', '15'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(redefinition_k4_subset_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.75/0.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.94       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.75/0.94          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 0.75/0.94          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 0.75/0.94      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.75/0.94            = (k2_xboole_0 @ sk_C @ X0))
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 0.75/0.94         = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.75/0.94      inference('sup-', [status(thm)], ['17', '20'])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['16', '21'])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t48_tops_1, axiom,
% 0.75/0.94    (![A:$i]:
% 0.75/0.94     ( ( l1_pre_topc @ A ) =>
% 0.75/0.94       ( ![B:$i]:
% 0.75/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94           ( ![C:$i]:
% 0.75/0.94             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/0.94               ( ( r1_tarski @ B @ C ) =>
% 0.75/0.94                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.75/0.94          | ~ (r1_tarski @ X23 @ X25)
% 0.75/0.94          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 0.75/0.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.75/0.94          | ~ (l1_pre_topc @ X24))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (l1_pre_topc @ sk_A)
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.94          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.75/0.94          | ~ (r1_tarski @ sk_C @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/0.94          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.75/0.94          | ~ (r1_tarski @ sk_C @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['25', '26'])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D))
% 0.75/0.94        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.75/0.94           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['22', '27'])).
% 0.75/0.94  thf(t7_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.75/0.94        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))),
% 0.75/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.94  thf(t3_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X14 : $i, X16 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_subset])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf(t5_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.75/0.94          ( v1_xboole_0 @ C ) ) ))).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X20 @ X21)
% 0.75/0.94          | ~ (v1_xboole_0 @ X22)
% 0.75/0.94          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t5_subset])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['32', '33'])).
% 0.75/0.94  thf('35', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.75/0.94      inference('clc', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf(t4_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.75/0.94       ( m1_subset_1 @ A @ C ) ))).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X17 @ X18)
% 0.75/0.94          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.75/0.94          | (m1_subset_1 @ X17 @ X19))),
% 0.75/0.94      inference('cnf', [status(esa)], [t4_subset])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      ((m1_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['35', '38'])).
% 0.75/0.94  thf(t2_subset, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( m1_subset_1 @ A @ B ) =>
% 0.75/0.94       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X12 : $i, X13 : $i]:
% 0.75/0.94         ((r2_hidden @ X12 @ X13)
% 0.75/0.94          | (v1_xboole_0 @ X13)
% 0.75/0.94          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_subset])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D) @ 
% 0.75/0.94        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['16', '21'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.94         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.75/0.94          | ~ (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 0.75/0.94          | (m1_connsp_2 @ X28 @ X27 @ X26)
% 0.75/0.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.75/0.94          | ~ (l1_pre_topc @ X27)
% 0.75/0.94          | ~ (v2_pre_topc @ X27)
% 0.75/0.94          | (v2_struct_0 @ X27))),
% 0.75/0.94      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v2_struct_0 @ sk_A)
% 0.75/0.94          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.94          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.94          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A @ X0)
% 0.75/0.94          | ~ (r2_hidden @ X0 @ 
% 0.75/0.94               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.94  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((v2_struct_0 @ sk_A)
% 0.75/0.94          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A @ X0)
% 0.75/0.94          | ~ (r2_hidden @ X0 @ 
% 0.75/0.94               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.75/0.94        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A @ sk_B)
% 0.75/0.94        | (v2_struct_0 @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['41', '47'])).
% 0.75/0.94  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))
% 0.75/0.94        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A @ sk_B)
% 0.75/0.94        | (v2_struct_0 @ sk_A))),
% 0.75/0.94      inference('demod', [status(thm)], ['48', '49'])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D) @ 
% 0.75/0.94          sk_A @ sk_B)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D)
% 0.75/0.94         = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.75/0.94      inference('sup-', [status(thm)], ['17', '20'])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D) @ sk_A @ sk_B)),
% 0.75/0.94      inference('demod', [status(thm)], ['51', '52'])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (((v2_struct_0 @ sk_A)
% 0.75/0.94        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D))))),
% 0.75/0.94      inference('clc', [status(thm)], ['50', '53'])).
% 0.75/0.94  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D)))),
% 0.75/0.94      inference('clc', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.75/0.94      inference('demod', [status(thm)], ['34', '56'])).
% 0.75/0.94  thf('58', plain, ($false), inference('sup-', [status(thm)], ['11', '57'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
