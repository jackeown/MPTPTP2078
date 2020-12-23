%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.knkQVtjmKf

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 449 expanded)
%              Number of leaves         :   39 ( 145 expanded)
%              Depth                    :   20
%              Number of atoms          : 1742 (6652 expanded)
%              Number of equality atoms :   65 ( 126 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t107_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v3_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v6_tops_1 @ D @ B ) )
                    & ( ( v6_tops_1 @ C @ A )
                     => ( ( v3_pre_topc @ C @ A )
                        & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( v3_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v6_tops_1 @ D @ B ) )
                      & ( ( v6_tops_1 @ C @ A )
                       => ( ( v3_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v6_tops_1 @ X28 @ X29 )
      | ( X28
        = ( k1_tops_1 @ X29 @ ( k2_pre_topc @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('18',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('36',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ X33 )
      | ( v4_pre_topc @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['54','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('66',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('68',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X27 @ ( k2_pre_topc @ X27 @ X26 ) ) @ X26 )
      | ~ ( r1_tarski @ X26 @ ( k2_pre_topc @ X27 @ ( k1_tops_1 @ X27 @ X26 ) ) )
      | ( v4_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('76',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X20 @ ( k2_pre_topc @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['74','79','80','82'])).

thf('84',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('88',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('89',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('91',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('92',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['94'])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    r1_tarski @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    = sk_D ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['96','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('108',plain,
    ( ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('117',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['113','114','117'])).

thf('119',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['110','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('122',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_xboole_0 @ sk_D @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( k3_xboole_0 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    = sk_D ),
    inference('sup-',[status(thm)],['99','100'])).

thf('124',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
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

thf('131',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X20 @ ( k2_pre_topc @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['135','140'])).

thf('142',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['124','141'])).

thf('143',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['92'])).

thf('144',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_tops_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ ( k2_pre_topc @ X27 @ X26 ) ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('151',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( X28
       != ( k1_tops_1 @ X29 @ ( k2_pre_topc @ X29 @ X28 ) ) )
      | ( v6_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('155',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['84'])).

thf('161',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','86','89','90','91','93','95','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.knkQVtjmKf
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 726 iterations in 0.229s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.68  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(t107_tops_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( l1_pre_topc @ B ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68               ( ![D:$i]:
% 0.46/0.68                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.68                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.46/0.68                       ( v6_tops_1 @ D @ B ) ) & 
% 0.46/0.68                     ( ( v6_tops_1 @ C @ A ) =>
% 0.46/0.68                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( l1_pre_topc @ B ) =>
% 0.46/0.68              ( ![C:$i]:
% 0.46/0.68                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68                  ( ![D:$i]:
% 0.46/0.68                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.68                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.46/0.68                          ( v6_tops_1 @ D @ B ) ) & 
% 0.46/0.68                        ( ( v6_tops_1 @ C @ A ) =>
% 0.46/0.68                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.46/0.68  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['2'])).
% 0.46/0.68  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['4'])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d8_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v6_tops_1 @ B @ A ) <=>
% 0.46/0.68             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.68          | ~ (v6_tops_1 @ X28 @ X29)
% 0.46/0.68          | ((X28) = (k1_tops_1 @ X29 @ (k2_pre_topc @ X29 @ X28)))
% 0.46/0.68          | ~ (l1_pre_topc @ X29))),
% 0.46/0.68      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.46/0.68        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.46/0.68        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '10'])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k2_pre_topc, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.68       ( m1_subset_1 @
% 0.46/0.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X18)
% 0.46/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.68          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.46/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.68  thf(fc9_tops_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.68       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X30 : $i, X31 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X30)
% 0.46/0.68          | ~ (v2_pre_topc @ X30)
% 0.46/0.68          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.46/0.68          | (v3_pre_topc @ (k1_tops_1 @ X30 @ X31) @ X30))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.46/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['11', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t3_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X15 : $i, X16 : $i]:
% 0.46/0.68         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('25', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.68  thf(t28_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('27', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf(commutativity_k2_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.68  thf(t12_setfam_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf(t36_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.46/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X15 : $i, X17 : $i]:
% 0.46/0.68         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf(t29_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.68             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X32 : $i, X33 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.46/0.68          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X33) @ X32) @ X33)
% 0.46/0.68          | (v4_pre_topc @ X32 @ X33)
% 0.46/0.68          | ~ (l1_pre_topc @ X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X0)
% 0.46/0.68          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.46/0.68          | ~ (v3_pre_topc @ 
% 0.46/0.68               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.46/0.68                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.46/0.68               X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf(d5_subset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i]:
% 0.46/0.68         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.46/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.68           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.68  thf(t48_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.68           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.68           = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X0)
% 0.46/0.68          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.46/0.68          | ~ (v3_pre_topc @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['37', '42'])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v3_pre_topc @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.46/0.68          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.46/0.68          | ~ (l1_pre_topc @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['32', '43'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['27', '44'])).
% 0.46/0.68  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '47'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf(t52_pre_topc, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X22 : $i, X23 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.68          | ~ (v4_pre_topc @ X22 @ X23)
% 0.46/0.68          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.46/0.68          | ~ (l1_pre_topc @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X0)
% 0.46/0.68          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.46/0.68              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.46/0.68          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.68           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.68         | ~ (l1_pre_topc @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['48', '51'])).
% 0.46/0.68  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.46/0.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d1_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.68             ( k3_subset_1 @
% 0.46/0.68               ( u1_struct_0 @ A ) @ 
% 0.46/0.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.68          | ((k1_tops_1 @ X25 @ X24)
% 0.46/0.68              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.46/0.68                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.46/0.68          | ~ (l1_pre_topc @ X25))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_C)
% 0.46/0.68            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68               (k2_pre_topc @ sk_A @ 
% 0.46/0.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.68  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i]:
% 0.46/0.68         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.46/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.46/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_A @ sk_C)
% 0.46/0.68         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.46/0.68      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.46/0.68          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.68           = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.46/0.68          = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.46/0.68  thf('67', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d6_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v4_tops_1 @ B @ A ) <=>
% 0.46/0.68             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.46/0.68               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (![X26 : $i, X27 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.68          | ~ (r1_tarski @ (k1_tops_1 @ X27 @ (k2_pre_topc @ X27 @ X26)) @ X26)
% 0.46/0.68          | ~ (r1_tarski @ X26 @ (k2_pre_topc @ X27 @ (k1_tops_1 @ X27 @ X26)))
% 0.46/0.68          | (v4_tops_1 @ X26 @ X27)
% 0.46/0.68          | ~ (l1_pre_topc @ X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | (v4_tops_1 @ sk_C @ sk_A)
% 0.46/0.68        | ~ (r1_tarski @ sk_C @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.46/0.68        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.46/0.68             sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_C @ sk_A)
% 0.46/0.68        | ~ (r1_tarski @ sk_C @ 
% 0.46/0.68             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.46/0.68        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.46/0.68             sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.46/0.68         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.46/0.68              sk_C)
% 0.46/0.68         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['68', '73'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t48_pre_topc, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.68          | (r1_tarski @ X20 @ (k2_pre_topc @ X21 @ X20))
% 0.46/0.68          | ~ (l1_pre_topc @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.68  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('79', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.46/0.68         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '10'])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('82', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.68      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['74', '79', '80', '82'])).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.46/0.68        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['84'])).
% 0.46/0.68  thf('86', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['83', '85'])).
% 0.46/0.68  thf('87', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['11', '21'])).
% 0.46/0.68  thf('88', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['84'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['4'])).
% 0.46/0.68  thf('91', plain,
% 0.46/0.68      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.46/0.68       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['84'])).
% 0.46/0.68  thf('92', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_D @ sk_B)
% 0.46/0.68        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.46/0.68       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['92'])).
% 0.46/0.68  thf('94', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_D @ sk_B)
% 0.46/0.68        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.46/0.68       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['94'])).
% 0.46/0.68  thf('96', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['94'])).
% 0.46/0.68  thf('97', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('98', plain,
% 0.46/0.68      (![X15 : $i, X16 : $i]:
% 0.46/0.68         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('99', plain, ((r1_tarski @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.68  thf('100', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('101', plain, (((k3_xboole_0 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v3_pre_topc @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.46/0.68          | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.46/0.68          | ~ (l1_pre_topc @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['32', '43'])).
% 0.46/0.68  thf('103', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.68  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('105', plain,
% 0.46/0.68      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.46/0.68        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['103', '104'])).
% 0.46/0.68  thf('106', plain,
% 0.46/0.68      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['96', '105'])).
% 0.46/0.68  thf('107', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X0)
% 0.46/0.68          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.46/0.68              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.46/0.68          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.68  thf('108', plain,
% 0.46/0.68      (((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.68           = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.68         | ~ (l1_pre_topc @ sk_B))) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.68  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('110', plain,
% 0.46/0.68      ((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.68  thf('111', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('112', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.68          | ((k1_tops_1 @ X25 @ X24)
% 0.46/0.68              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.46/0.68                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.46/0.68          | ~ (l1_pre_topc @ X25))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.46/0.68  thf('113', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | ((k1_tops_1 @ sk_B @ sk_D)
% 0.46/0.68            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.68               (k2_pre_topc @ sk_B @ 
% 0.46/0.68                (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.68  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('115', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('116', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i]:
% 0.46/0.68         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.46/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.68  thf('117', plain,
% 0.46/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.46/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.68  thf('118', plain,
% 0.46/0.68      (((k1_tops_1 @ sk_B @ sk_D)
% 0.46/0.68         = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.68            (k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.46/0.68      inference('demod', [status(thm)], ['113', '114', '117'])).
% 0.46/0.68  thf('119', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.46/0.68          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.68             (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['110', '118'])).
% 0.46/0.68  thf('120', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.68           = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('121', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('122', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.46/0.68          = (k3_xboole_0 @ sk_D @ (u1_struct_0 @ sk_B))))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.46/0.68  thf('123', plain, (((k3_xboole_0 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('124', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['122', '123'])).
% 0.46/0.68  thf('125', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('126', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X18)
% 0.46/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.68          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.68  thf('127', plain,
% 0.46/0.68      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.46/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.68        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.68  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('129', plain,
% 0.46/0.68      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['127', '128'])).
% 0.46/0.68  thf('130', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t48_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68               ( ( r1_tarski @ B @ C ) =>
% 0.46/0.68                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('131', plain,
% 0.46/0.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.68          | ~ (r1_tarski @ X34 @ X36)
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ (k1_tops_1 @ X35 @ X36))
% 0.46/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.68          | ~ (l1_pre_topc @ X35))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.46/0.68  thf('132', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ sk_B)
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.46/0.68          | ~ (r1_tarski @ sk_D @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.68  thf('133', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('134', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.46/0.68          | ~ (r1_tarski @ sk_D @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.46/0.68  thf('135', plain,
% 0.46/0.68      ((~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))
% 0.46/0.68        | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.46/0.68           (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['129', '134'])).
% 0.46/0.68  thf('136', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('137', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.68          | (r1_tarski @ X20 @ (k2_pre_topc @ X21 @ X20))
% 0.46/0.68          | ~ (l1_pre_topc @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.68  thf('138', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.68  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('140', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.46/0.68  thf('141', plain,
% 0.46/0.68      ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.46/0.68        (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.46/0.68      inference('demod', [status(thm)], ['135', '140'])).
% 0.46/0.68  thf('142', plain,
% 0.46/0.68      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.46/0.68         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['124', '141'])).
% 0.46/0.68  thf('143', plain,
% 0.46/0.68      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['92'])).
% 0.46/0.68  thf('144', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('145', plain,
% 0.46/0.68      (![X26 : $i, X27 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.68          | ~ (v4_tops_1 @ X26 @ X27)
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ X27 @ (k2_pre_topc @ X27 @ X26)) @ X26)
% 0.46/0.68          | ~ (l1_pre_topc @ X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.46/0.68  thf('146', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.46/0.68        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['144', '145'])).
% 0.46/0.68  thf('147', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('148', plain,
% 0.46/0.68      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.46/0.68        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['146', '147'])).
% 0.46/0.68  thf('149', plain,
% 0.46/0.68      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.46/0.68         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['143', '148'])).
% 0.46/0.68  thf('150', plain,
% 0.46/0.68      (![X0 : $i, X2 : $i]:
% 0.46/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('151', plain,
% 0.46/0.68      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.46/0.68         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.46/0.68         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['149', '150'])).
% 0.46/0.68  thf('152', plain,
% 0.46/0.68      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.46/0.68         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['142', '151'])).
% 0.46/0.68  thf('153', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('154', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.68          | ((X28) != (k1_tops_1 @ X29 @ (k2_pre_topc @ X29 @ X28)))
% 0.46/0.68          | (v6_tops_1 @ X28 @ X29)
% 0.46/0.68          | ~ (l1_pre_topc @ X29))),
% 0.46/0.68      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.46/0.68  thf('155', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (v6_tops_1 @ sk_D @ sk_B)
% 0.46/0.68        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['153', '154'])).
% 0.46/0.68  thf('156', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('157', plain,
% 0.46/0.68      (((v6_tops_1 @ sk_D @ sk_B)
% 0.46/0.68        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.46/0.68      inference('demod', [status(thm)], ['155', '156'])).
% 0.46/0.68  thf('158', plain,
% 0.46/0.68      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.46/0.68         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['152', '157'])).
% 0.46/0.68  thf('159', plain,
% 0.46/0.68      (((v6_tops_1 @ sk_D @ sk_B))
% 0.46/0.68         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['158'])).
% 0.46/0.68  thf('160', plain,
% 0.46/0.68      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['84'])).
% 0.46/0.68  thf('161', plain,
% 0.46/0.68      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.46/0.68       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['159', '160'])).
% 0.46/0.68  thf('162', plain, ($false),
% 0.46/0.68      inference('sat_resolution*', [status(thm)],
% 0.46/0.68                ['1', '3', '86', '89', '90', '91', '93', '95', '161'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
