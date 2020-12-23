%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DEZf7xqpMj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 206 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   19
%              Number of atoms          : 1132 (3821 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X26 @ sk_A )
      | ~ ( r1_tarski @ X26 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X26 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('31',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','34','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
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

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ sk_D @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','58'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['42','78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','40','41','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DEZf7xqpMj
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:14:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 154 iterations in 0.077s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(t8_connsp_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( ?[D:$i]:
% 0.21/0.54                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.54                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                    ( ?[D:$i]:
% 0.21/0.54                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.54                        ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                        ( m1_subset_1 @
% 0.21/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.54       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X26 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54          | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54          | ~ (r2_hidden @ sk_B @ X26)
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((![X26 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.21/0.54       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['8'])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.21/0.54          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.54          | ~ (l1_pre_topc @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.54  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_tops_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X11)
% 0.21/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.54          | (m1_subset_1 @ (k1_tops_1 @ X11 @ X12) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      ((![X26 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X26)))
% 0.21/0.54         <= ((![X26 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.21/0.54         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.21/0.54         <= ((![X26 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.21/0.54         <= ((![X26 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X26))) & 
% 0.21/0.54             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(fc9_tops_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X13)
% 0.21/0.54          | ~ (v2_pre_topc @ X13)
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.54          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t44_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.54          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 0.21/0.54          | ~ (l1_pre_topc @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('39', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X26 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.21/0.54       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '34', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['8'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.54      inference('split', [status(esa)], ['8'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.54      inference('split', [status(esa)], ['8'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf(t56_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.54                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.54          | ~ (v3_pre_topc @ X17 @ X18)
% 0.21/0.54          | ~ (r1_tarski @ X17 @ X19)
% 0.21/0.54          | (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.54          | ~ (l1_pre_topc @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (l1_pre_topc @ sk_A)
% 0.21/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.54           | ~ (r1_tarski @ sk_D @ X0)
% 0.21/0.54           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.21/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.54           | ~ (r1_tarski @ sk_D @ X0)
% 0.21/0.54           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.21/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (r1_tarski @ sk_D @ X0)
% 0.21/0.54           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.54         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | ~ (r1_tarski @ sk_D @ sk_C)))
% 0.21/0.54         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '53'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X2 : $i, X4 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.54          | (m1_subset_1 @ X5 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          ((m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['43', '58'])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ X1)
% 0.21/0.54          | (v1_xboole_0 @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.54          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.21/0.54          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.54          | ~ (l1_pre_topc @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21)
% 0.21/0.54          | (v2_struct_0 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.54  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '67'])).
% 0.21/0.54  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54         | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.21/0.54             ((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf(t5_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.54          | ~ (v1_xboole_0 @ X10)
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.21/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.21/0.54             ((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.21/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.21/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['74', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (~ ((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.54       ~ ((v3_pre_topc @ sk_D @ sk_A)) | ~ ((r1_tarski @ sk_D @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['42', '78'])).
% 0.21/0.54  thf('80', plain, ($false),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['1', '3', '5', '7', '40', '41', '79'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
