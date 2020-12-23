%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t7Z42BTh1e

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:39 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 178 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  725 (2802 expanded)
%              Number of equality atoms :   28 ( 101 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) )
               => ( B
                  = ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( k1_tops_2 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) )
                 => ( B
                    = ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( k1_tops_2 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X21 @ X20 @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X21 @ X20 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X19 @ X18 ) )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X4 ) @ ( k3_tarski @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) )
    | ( sk_B
      = ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B
 != ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    sk_B
 != ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k5_setfam_1 @ X14 @ X13 )
        = ( k3_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('26',plain,
    ( ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) )
    = ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B
 != ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ D ) )
                   => ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) @ ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X26 ) ) @ ( k1_tops_2 @ X24 @ X26 @ X25 ) ) )
      | ~ ( r1_tarski @ X23 @ ( k5_setfam_1 @ ( u1_struct_0 @ X24 ) @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_tops_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k5_setfam_1 @ X14 @ X13 )
        = ( k3_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('37',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k3_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X1 @ ( k3_tarski @ sk_C ) )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) @ ( k1_tops_2 @ sk_A @ X0 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k5_setfam_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,
    ( ( k5_setfam_1 @ sk_B @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) )
    = ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['39','42','43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_tarski @ sk_C ) )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_B ) @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','45'])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k3_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['28','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t7Z42BTh1e
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.73/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.73/1.92  % Solved by: fo/fo7.sh
% 1.73/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.92  % done 1425 iterations in 1.457s
% 1.73/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.73/1.92  % SZS output start Refutation
% 1.73/1.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.92  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.73/1.92  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.73/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.73/1.92  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 1.73/1.92  thf(sk_C_type, type, sk_C: $i).
% 1.73/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.73/1.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.73/1.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.73/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.73/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.73/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.92  thf(t43_tops_2, conjecture,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ![C:$i]:
% 1.73/1.92             ( ( m1_subset_1 @
% 1.73/1.92                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.73/1.92               ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) =>
% 1.73/1.92                 ( ( B ) =
% 1.73/1.92                   ( k5_setfam_1 @
% 1.73/1.92                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 1.73/1.92                     ( k1_tops_2 @ A @ B @ C ) ) ) ) ) ) ) ) ))).
% 1.73/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.92    (~( ![A:$i]:
% 1.73/1.92        ( ( l1_pre_topc @ A ) =>
% 1.73/1.92          ( ![B:$i]:
% 1.73/1.92            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92              ( ![C:$i]:
% 1.73/1.92                ( ( m1_subset_1 @
% 1.73/1.92                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.73/1.92                  ( ( r1_tarski @ B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) =>
% 1.73/1.92                    ( ( B ) =
% 1.73/1.92                      ( k5_setfam_1 @
% 1.73/1.92                        ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 1.73/1.92                        ( k1_tops_2 @ A @ B @ C ) ) ) ) ) ) ) ) ) )),
% 1.73/1.92    inference('cnf.neg', [status(esa)], [t43_tops_2])).
% 1.73/1.92  thf('0', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('1', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_C @ 
% 1.73/1.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(dt_k1_tops_2, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( ( l1_pre_topc @ A ) & 
% 1.73/1.92         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.73/1.92         ( m1_subset_1 @
% 1.73/1.92           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.73/1.92       ( m1_subset_1 @
% 1.73/1.92         ( k1_tops_2 @ A @ B @ C ) @ 
% 1.73/1.92         ( k1_zfmisc_1 @
% 1.73/1.92           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 1.73/1.92  thf('2', plain,
% 1.73/1.92      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.73/1.92          | ~ (l1_pre_topc @ X21)
% 1.73/1.92          | ~ (m1_subset_1 @ X22 @ 
% 1.73/1.92               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 1.73/1.92          | (m1_subset_1 @ (k1_tops_2 @ X21 @ X20 @ X22) @ 
% 1.73/1.92             (k1_zfmisc_1 @ 
% 1.73/1.92              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X21 @ X20))))))),
% 1.73/1.92      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 1.73/1.92  thf('3', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_C) @ 
% 1.73/1.92           (k1_zfmisc_1 @ 
% 1.73/1.92            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 1.73/1.92          | ~ (l1_pre_topc @ sk_A)
% 1.73/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['1', '2'])).
% 1.73/1.92  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('5', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_C) @ 
% 1.73/1.92           (k1_zfmisc_1 @ 
% 1.73/1.92            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 1.73/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['3', '4'])).
% 1.73/1.92  thf('6', plain,
% 1.73/1.92      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ 
% 1.73/1.92        (k1_zfmisc_1 @ 
% 1.73/1.92         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['0', '5'])).
% 1.73/1.92  thf('7', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t29_pre_topc, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.73/1.92  thf('8', plain,
% 1.73/1.92      (![X18 : $i, X19 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.73/1.92          | ((u1_struct_0 @ (k1_pre_topc @ X19 @ X18)) = (X18))
% 1.73/1.92          | ~ (l1_pre_topc @ X19))),
% 1.73/1.92      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.73/1.92  thf('9', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['7', '8'])).
% 1.73/1.92  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('11', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('12', plain,
% 1.73/1.92      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['6', '11'])).
% 1.73/1.92  thf(t3_subset, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.73/1.92  thf('13', plain,
% 1.73/1.92      (![X15 : $i, X16 : $i]:
% 1.73/1.92         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t3_subset])).
% 1.73/1.92  thf('14', plain,
% 1.73/1.92      ((r1_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['12', '13'])).
% 1.73/1.92  thf(t95_zfmisc_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( r1_tarski @ A @ B ) =>
% 1.73/1.92       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.73/1.92  thf('15', plain,
% 1.73/1.92      (![X4 : $i, X5 : $i]:
% 1.73/1.92         ((r1_tarski @ (k3_tarski @ X4) @ (k3_tarski @ X5))
% 1.73/1.92          | ~ (r1_tarski @ X4 @ X5))),
% 1.73/1.92      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 1.73/1.92  thf('16', plain,
% 1.73/1.92      ((r1_tarski @ (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ 
% 1.73/1.92        (k3_tarski @ (k1_zfmisc_1 @ sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['14', '15'])).
% 1.73/1.92  thf(t99_zfmisc_1, axiom,
% 1.73/1.92    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.73/1.92  thf('17', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 1.73/1.92      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.73/1.92  thf('18', plain,
% 1.73/1.92      ((r1_tarski @ (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)) @ sk_B)),
% 1.73/1.92      inference('demod', [status(thm)], ['16', '17'])).
% 1.73/1.92  thf(d10_xboole_0, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.73/1.92  thf('19', plain,
% 1.73/1.92      (![X1 : $i, X3 : $i]:
% 1.73/1.92         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.73/1.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.73/1.92  thf('20', plain,
% 1.73/1.92      ((~ (r1_tarski @ sk_B @ (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))
% 1.73/1.92        | ((sk_B) = (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['18', '19'])).
% 1.73/1.92  thf('21', plain,
% 1.73/1.92      (((sk_B)
% 1.73/1.92         != (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.73/1.92             (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('22', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('23', plain,
% 1.73/1.92      (((sk_B) != (k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('demod', [status(thm)], ['21', '22'])).
% 1.73/1.92  thf('24', plain,
% 1.73/1.92      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_B @ sk_C) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 1.73/1.92      inference('demod', [status(thm)], ['6', '11'])).
% 1.73/1.92  thf(redefinition_k5_setfam_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.73/1.92       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.73/1.92  thf('25', plain,
% 1.73/1.92      (![X13 : $i, X14 : $i]:
% 1.73/1.92         (((k5_setfam_1 @ X14 @ X13) = (k3_tarski @ X13))
% 1.73/1.92          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.73/1.92  thf('26', plain,
% 1.73/1.92      (((k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C))
% 1.73/1.92         = (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['24', '25'])).
% 1.73/1.92  thf('27', plain,
% 1.73/1.92      (((sk_B) != (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('demod', [status(thm)], ['23', '26'])).
% 1.73/1.92  thf('28', plain,
% 1.73/1.92      (~ (r1_tarski @ sk_B @ (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('simplify_reflect-', [status(thm)], ['20', '27'])).
% 1.73/1.92  thf('29', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('30', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('31', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_C @ 
% 1.73/1.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t42_tops_2, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ![C:$i]:
% 1.73/1.92             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92               ( ![D:$i]:
% 1.73/1.92                 ( ( m1_subset_1 @
% 1.73/1.92                     D @ 
% 1.73/1.92                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.73/1.92                   ( ( r1_tarski @
% 1.73/1.92                       B @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ D ) ) =>
% 1.73/1.92                     ( r1_tarski @
% 1.73/1.92                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 1.73/1.92                       ( k5_setfam_1 @
% 1.73/1.92                         ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) @ 
% 1.73/1.92                         ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 1.73/1.92  thf('32', plain,
% 1.73/1.92      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.73/1.92          | ~ (m1_subset_1 @ X25 @ 
% 1.73/1.92               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 1.73/1.92          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26) @ 
% 1.73/1.92             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X26)) @ 
% 1.73/1.92              (k1_tops_2 @ X24 @ X26 @ X25)))
% 1.73/1.92          | ~ (r1_tarski @ X23 @ (k5_setfam_1 @ (u1_struct_0 @ X24) @ X25))
% 1.73/1.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.73/1.92          | ~ (l1_pre_topc @ X24))),
% 1.73/1.92      inference('cnf', [status(esa)], [t42_tops_2])).
% 1.73/1.92  thf('33', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (l1_pre_topc @ sk_A)
% 1.73/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | ~ (r1_tarski @ X1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.73/1.92          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ 
% 1.73/1.92             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 1.73/1.92              (k1_tops_2 @ sk_A @ X0 @ sk_C)))
% 1.73/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['31', '32'])).
% 1.73/1.92  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('35', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_C @ 
% 1.73/1.92        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('36', plain,
% 1.73/1.92      (![X13 : $i, X14 : $i]:
% 1.73/1.92         (((k5_setfam_1 @ X14 @ X13) = (k3_tarski @ X13))
% 1.73/1.92          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.73/1.92  thf('37', plain,
% 1.73/1.92      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.73/1.92      inference('sup-', [status(thm)], ['35', '36'])).
% 1.73/1.92  thf('38', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | ~ (r1_tarski @ X1 @ (k3_tarski @ sk_C))
% 1.73/1.92          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ 
% 1.73/1.92             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)) @ 
% 1.73/1.92              (k1_tops_2 @ sk_A @ X0 @ sk_C)))
% 1.73/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['33', '34', '37'])).
% 1.73/1.92  thf('39', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 1.73/1.92             (k5_setfam_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.73/1.92              (k1_tops_2 @ sk_A @ sk_B @ sk_C)))
% 1.73/1.92          | ~ (r1_tarski @ X0 @ (k3_tarski @ sk_C)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['30', '38'])).
% 1.73/1.92  thf('40', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(redefinition_k9_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.73/1.92  thf('41', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.73/1.92         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 1.73/1.92          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.73/1.92  thf('42', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.73/1.92           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['40', '41'])).
% 1.73/1.92  thf('43', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('44', plain,
% 1.73/1.92      (((k5_setfam_1 @ sk_B @ (k1_tops_2 @ sk_A @ sk_B @ sk_C))
% 1.73/1.92         = (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['24', '25'])).
% 1.73/1.92  thf('45', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 1.73/1.92             (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))
% 1.73/1.92          | ~ (r1_tarski @ X0 @ (k3_tarski @ sk_C)))),
% 1.73/1.92      inference('demod', [status(thm)], ['39', '42', '43', '44'])).
% 1.73/1.92  thf('46', plain,
% 1.73/1.92      ((~ (r1_tarski @ sk_B @ (k3_tarski @ sk_C))
% 1.73/1.92        | (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_B) @ 
% 1.73/1.92           (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['29', '45'])).
% 1.73/1.92  thf('47', plain,
% 1.73/1.92      ((r1_tarski @ sk_B @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('48', plain,
% 1.73/1.92      (((k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k3_tarski @ sk_C))),
% 1.73/1.92      inference('sup-', [status(thm)], ['35', '36'])).
% 1.73/1.92  thf('49', plain, ((r1_tarski @ sk_B @ (k3_tarski @ sk_C))),
% 1.73/1.92      inference('demod', [status(thm)], ['47', '48'])).
% 1.73/1.92  thf(idempotence_k3_xboole_0, axiom,
% 1.73/1.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.73/1.92  thf('50', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.73/1.92      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.73/1.92  thf('51', plain,
% 1.73/1.92      ((r1_tarski @ sk_B @ (k3_tarski @ (k1_tops_2 @ sk_A @ sk_B @ sk_C)))),
% 1.73/1.92      inference('demod', [status(thm)], ['46', '49', '50'])).
% 1.73/1.92  thf('52', plain, ($false), inference('demod', [status(thm)], ['28', '51'])).
% 1.73/1.92  
% 1.73/1.92  % SZS output end Refutation
% 1.73/1.92  
% 1.73/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
