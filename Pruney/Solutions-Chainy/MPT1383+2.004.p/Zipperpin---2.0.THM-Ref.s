%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lU5WdHNisc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 198 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          : 1199 (3762 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t8_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m1_connsp_2 @ C @ A @ B )
                <=> ? [D: $i] :
                      ( ( r2_hidden @ B @ D )
                      & ( r1_tarski @ D @ C )
                      & ( v3_pre_topc @ D @ A )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_connsp_2])).

thf('0',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) )
   <= ( ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X20 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k1_tops_1 @ X13 @ X12 )
       != X12 )
      | ( v3_pre_topc @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('31',plain,
    ( ! [X12: $i,X13: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( l1_pre_topc @ X13 )
        | ~ ( v2_pre_topc @ X13 )
        | ( ( k1_tops_1 @ X13 @ X12 )
         != X12 )
        | ( v3_pre_topc @ X12 @ X13 ) )
   <= ! [X12: $i,X13: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( l1_pre_topc @ X13 )
        | ~ ( v2_pre_topc @ X13 )
        | ( ( k1_tops_1 @ X13 @ X12 )
         != X12 )
        | ( v3_pre_topc @ X12 @ X13 ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ! [X10: $i,X11: $i] :
        ( ~ ( l1_pre_topc @ X10 )
        | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
   <= ! [X10: $i,X11: $i] :
        ( ~ ( l1_pre_topc @ X10 )
        | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X10: $i,X11: $i] :
        ( ~ ( l1_pre_topc @ X10 )
        | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ! [X10: $i,X11: $i] :
        ( ~ ( l1_pre_topc @ X10 )
        | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X12: $i,X13: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( l1_pre_topc @ X13 )
        | ~ ( v2_pre_topc @ X13 )
        | ( ( k1_tops_1 @ X13 @ X12 )
         != X12 )
        | ( v3_pre_topc @ X12 @ X13 ) )
    | ! [X10: $i,X11: $i] :
        ( ~ ( l1_pre_topc @ X10 )
        | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( ( k1_tops_1 @ X13 @ X12 )
       != X12 )
      | ( v3_pre_topc @ X12 @ X13 ) ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( ( k1_tops_1 @ X13 @ X12 )
       != X12 )
      | ( v3_pre_topc @ X12 @ X13 ) ) ),
    inference(simpl_trail,[status(thm)],['31','38'])).

thf('40',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
     != ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
     != ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k1_tops_1 @ X6 @ ( k1_tops_1 @ X6 @ X7 ) )
        = ( k1_tops_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C_1 )
     != ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X20 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','50','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('59',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

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

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_D @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','56','57','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lU5WdHNisc
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 132 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(t8_connsp_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.50                 ( ?[D:$i]:
% 0.20/0.50                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.50                     ( v3_pre_topc @ D @ A ) & 
% 0.20/0.50                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.50                    ( ?[D:$i]:
% 0.20/0.50                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.50                        ( v3_pre_topc @ D @ A ) & 
% 0.20/0.50                        ( m1_subset_1 @
% 0.20/0.50                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((r1_tarski @ sk_D @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r1_tarski @ sk_D @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.50       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50          | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50          | ~ (r2_hidden @ sk_B @ X20)
% 0.20/0.50          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ sk_B @ X20))) | 
% 0.20/0.50       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.50         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d1_connsp_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.50                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.50          | ~ (m1_connsp_2 @ X19 @ X18 @ X17)
% 0.20/0.50          | (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.50          | ~ (l1_pre_topc @ X18)
% 0.20/0.50          | ~ (v2_pre_topc @ X18)
% 0.20/0.50          | (v2_struct_0 @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.50         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.50  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.50         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k1_tops_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X4)
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.50          | (m1_subset_1 @ (k1_tops_1 @ X4 @ X5) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50           | ~ (r2_hidden @ sk_B @ X20)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.20/0.50         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.50         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.50                 | ~ (r2_hidden @ sk_B @ X20))) & 
% 0.20/0.50             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf(t55_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.50                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.50                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.50                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.50          | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50          | (v3_pre_topc @ X12 @ X13)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((![X12 : $i, X13 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50           | ~ (l1_pre_topc @ X13)
% 0.20/0.50           | ~ (v2_pre_topc @ X13)
% 0.20/0.50           | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50           | (v3_pre_topc @ X12 @ X13)))
% 0.20/0.50         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50                 | ~ (l1_pre_topc @ X13)
% 0.20/0.50                 | ~ (v2_pre_topc @ X13)
% 0.20/0.50                 | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50                 | (v3_pre_topc @ X12 @ X13))))),
% 0.20/0.50      inference('split', [status(esa)], ['30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((![X10 : $i, X11 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X10)
% 0.20/0.50           | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))))
% 0.20/0.50         <= ((![X10 : $i, X11 : $i]:
% 0.20/0.50                (~ (l1_pre_topc @ X10)
% 0.20/0.50                 | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))))),
% 0.20/0.50      inference('split', [status(esa)], ['30'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A))
% 0.20/0.50         <= ((![X10 : $i, X11 : $i]:
% 0.20/0.50                (~ (l1_pre_topc @ X10)
% 0.20/0.50                 | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X10 : $i, X11 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X10)
% 0.20/0.50           | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((![X12 : $i, X13 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50           | ~ (l1_pre_topc @ X13)
% 0.20/0.50           | ~ (v2_pre_topc @ X13)
% 0.20/0.50           | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50           | (v3_pre_topc @ X12 @ X13))) | 
% 0.20/0.50       (![X10 : $i, X11 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X10)
% 0.20/0.50           | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))))),
% 0.20/0.50      inference('split', [status(esa)], ['30'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((![X12 : $i, X13 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50           | ~ (l1_pre_topc @ X13)
% 0.20/0.50           | ~ (v2_pre_topc @ X13)
% 0.20/0.50           | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50           | (v3_pre_topc @ X12 @ X13)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.50          | ~ (l1_pre_topc @ X13)
% 0.20/0.50          | ~ (v2_pre_topc @ X13)
% 0.20/0.50          | ((k1_tops_1 @ X13 @ X12) != (X12))
% 0.20/0.50          | (v3_pre_topc @ X12 @ X13))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['31', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50            != (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '39'])).
% 0.20/0.50  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50            != (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(projectivity_k1_tops_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.50          | ((k1_tops_1 @ X6 @ (k1_tops_1 @ X6 @ X7)) = (k1_tops_1 @ X6 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50          = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.50         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_C_1) != (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '48'])).
% 0.20/0.51  thf('50', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.20/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t44_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.51          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ X8)
% 0.20/0.51          | ~ (l1_pre_topc @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (~
% 0.20/0.51       (![X20 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.51           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.20/0.51           | ~ (r2_hidden @ sk_B @ X20))) | 
% 0.20/0.51       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '50', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('split', [status(esa)], ['4'])).
% 0.20/0.51  thf(t56_tops_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | ~ (v3_pre_topc @ X14 @ X15)
% 0.20/0.51          | ~ (r1_tarski @ X14 @ X16)
% 0.20/0.51          | (r1_tarski @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | ~ (l1_pre_topc @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (l1_pre_topc @ sk_A)
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.51           | ~ (r1_tarski @ sk_D @ X0)
% 0.20/0.51           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.20/0.51         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.51           | ~ (r1_tarski @ sk_D @ X0)
% 0.20/0.51           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.20/0.51         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r1_tarski @ sk_D @ X0)
% 0.20/0.51           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.51         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['61', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51         | ~ (r1_tarski @ sk_D @ sk_C_1)))
% 0.20/0.51         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '68'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.20/0.51         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.20/0.51             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.51          | (m1_connsp_2 @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (l1_pre_topc @ X18)
% 0.20/0.51          | ~ (v2_pre_topc @ X18)
% 0.20/0.51          | (v2_struct_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.20/0.51             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['72', '78'])).
% 0.20/0.51  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.20/0.51             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.51  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.20/0.51             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.20/0.51             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.20/0.51             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.51         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.20/0.51       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.51       ~ ((v3_pre_topc @ sk_D @ sk_A)) | ~ ((r1_tarski @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.51  thf('86', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)],
% 0.20/0.51                ['1', '3', '5', '7', '56', '57', '85'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
