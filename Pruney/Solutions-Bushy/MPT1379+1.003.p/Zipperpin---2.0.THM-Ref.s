%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1379+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S7QU7JaWFh

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:35 EST 2020

% Result     : Theorem 8.35s
% Output     : Refutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  185 (1144 expanded)
%              Number of leaves         :   24 ( 320 expanded)
%              Depth                    :   25
%              Number of atoms          : 2049 (21785 expanded)
%              Number of equality atoms :   48 ( 500 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t4_connsp_2,conjecture,(
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
                  <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

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
                    <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) )
                = ( k1_tops_1 @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
        = ( k1_tops_1 @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X22 @ X20 @ X21 )
        = ( k3_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ X0 ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
        = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','51'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('54',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('73',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','71','72'])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','71','72'])).

thf('93',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('106',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','118'])).

thf('120',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['92','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('122',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('136',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('137',plain,
    ( ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('140',plain,(
    m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['24','90','91','138','139'])).

thf('141',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(simpl_trail,[status(thm)],['22','140'])).

thf('142',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','71','72'])).

thf('143',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tops_1 @ X4 @ X5 ) )
      | ( m1_connsp_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('156',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24','90','91','138'])).

thf('157',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['154','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['0','158'])).


%------------------------------------------------------------------------------
