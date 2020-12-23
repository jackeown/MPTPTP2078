%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1aMNampNIt

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 300 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          : 1387 (5847 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D_1 @ X0 )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D_1 @ X0 )
        | ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,
    ( ( ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_D_1 @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D_1 ) )
   <= ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D_1 )
      & ( r1_tarski @ sk_D_1 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( r1_tarski @ X25 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X25 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('44',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( m1_connsp_2 @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 @ X22 )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_connsp_2 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('77',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X25 ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X25 ) ) ),
    inference(split,[status(esa)],['40'])).

thf('78',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v3_pre_topc @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( v3_pre_topc @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( v3_pre_topc @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','90'])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','91'])).

thf('93',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_tarski @ ( sk_D @ X24 @ X22 @ X23 ) @ X24 )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
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
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X25 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','104'])).

thf('106',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','42','43','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1aMNampNIt
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 320 iterations in 0.099s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.55  thf(t8_connsp_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.55                 ( ?[D:$i]:
% 0.35/0.55                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.35/0.55                     ( v3_pre_topc @ D @ A ) & 
% 0.35/0.55                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55              ( ![C:$i]:
% 0.35/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.55                    ( ?[D:$i]:
% 0.35/0.55                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.35/0.55                        ( v3_pre_topc @ D @ A ) & 
% 0.35/0.55                        ( m1_subset_1 @
% 0.35/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D_1 @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D_1 @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D_1)) <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D_1 @ sk_A)) <= (((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t3_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X7 : $i, X8 : $i]:
% 0.35/0.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('11', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ sk_C_1)) <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf(t1_xboole_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.55       ( r1_tarski @ A @ C ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X4 @ X5)
% 0.35/0.55          | ~ (r1_tarski @ X5 @ X6)
% 0.35/0.55          | (r1_tarski @ X4 @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      ((![X0 : $i]: ((r1_tarski @ sk_D_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X7 : $i, X9 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf(t56_tops_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.55                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.55          | ~ (v3_pre_topc @ X10 @ X11)
% 0.35/0.55          | ~ (r1_tarski @ X10 @ X12)
% 0.35/0.55          | (r1_tarski @ X10 @ (k1_tops_1 @ X11 @ X12))
% 0.35/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.55          | ~ (l1_pre_topc @ X11))),
% 0.35/0.55      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (l1_pre_topc @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.55           | ~ (r1_tarski @ sk_D_1 @ X0)
% 0.35/0.55           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.55           | ~ (r1_tarski @ sk_D_1 @ X0)
% 0.35/0.55           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (r1_tarski @ sk_D_1 @ X0)
% 0.35/0.55           | (r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)) & ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['8', '21'])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      ((((r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.35/0.55         | ~ (r1_tarski @ sk_D_1 @ sk_C_1)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)) & ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '22'])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ sk_C_1)) <= (((r1_tarski @ sk_D_1 @ sk_C_1)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((r1_tarski @ sk_D_1 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)) & ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.55  thf(d3_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.55          | (r2_hidden @ X0 @ X2)
% 0.35/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.35/0.55           | ~ (r2_hidden @ X0 @ sk_D_1)))
% 0.35/0.55         <= (((r1_tarski @ sk_D_1 @ sk_C_1)) & ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.35/0.55             ((r1_tarski @ sk_D_1 @ sk_C_1)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '27'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d1_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.55                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.35/0.55          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.35/0.55          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.35/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.55          | ~ (l1_pre_topc @ X14)
% 0.35/0.55          | ~ (v2_pre_topc @ X14)
% 0.35/0.55          | (v2_struct_0 @ X14))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.55  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.35/0.55         | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.35/0.55             ((r1_tarski @ sk_D_1 @ sk_C_1)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['28', '34'])).
% 0.35/0.55  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.35/0.55             ((r1_tarski @ sk_D_1 @ sk_C_1)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D_1)) & 
% 0.35/0.55             ((r1_tarski @ sk_D_1 @ sk_C_1)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (![X25 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55          | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55          | ~ (r2_hidden @ sk_B @ X25)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.35/0.55         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (~ ((v3_pre_topc @ sk_D_1 @ sk_A)) | 
% 0.35/0.55       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.35/0.55       ~ ((r2_hidden @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_D_1 @ sk_C_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['39', '41'])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      ((![X25 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.35/0.55       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['40'])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t7_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.35/0.55                    ( ![D:$i]:
% 0.35/0.55                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.35/0.55                          ( m1_subset_1 @
% 0.35/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.35/0.55                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.35/0.55          | (m1_connsp_2 @ (sk_D @ X24 @ X22 @ X23) @ X23 @ X22)
% 0.35/0.55          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.35/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.55          | ~ (l1_pre_topc @ X23)
% 0.35/0.55          | ~ (v2_pre_topc @ X23)
% 0.35/0.55          | (v2_struct_0 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (m1_connsp_2 @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (m1_connsp_2 @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      (((m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.35/0.55        | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['45', '51'])).
% 0.35/0.55  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.35/0.55        | (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))),
% 0.35/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (((m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['44', '54'])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      (((m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['44', '54'])).
% 0.35/0.55  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_m1_connsp_2, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55       ( ![C:$i]:
% 0.35/0.55         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.35/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X16)
% 0.35/0.55          | ~ (v2_pre_topc @ X16)
% 0.35/0.55          | (v2_struct_0 @ X16)
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.35/0.55          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.55          | ~ (m1_connsp_2 @ X18 @ X16 @ X17))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | (v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.55  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.35/0.55          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.55  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('64', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.35/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      (((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['56', '64'])).
% 0.35/0.55  thf(t6_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.35/0.55          | ~ (m1_connsp_2 @ X19 @ X20 @ X21)
% 0.35/0.55          | (r2_hidden @ X21 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.35/0.55          | ~ (l1_pre_topc @ X20)
% 0.35/0.55          | ~ (v2_pre_topc @ X20)
% 0.35/0.55          | (v2_struct_0 @ X20))),
% 0.35/0.55      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55           | (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55           | ~ (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ X0)))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.55  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55           | (r2_hidden @ X0 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55           | ~ (m1_connsp_2 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A @ X0)))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.35/0.55  thf('71', plain,
% 0.35/0.55      ((((r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['55', '70'])).
% 0.35/0.55  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('73', plain,
% 0.35/0.55      ((((r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.35/0.55  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('75', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('clc', [status(thm)], ['73', '74'])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      (((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['56', '64'])).
% 0.35/0.55  thf('77', plain,
% 0.35/0.55      ((![X25 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X25)))
% 0.35/0.55         <= ((![X25 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X25))))),
% 0.35/0.55      inference('split', [status(esa)], ['40'])).
% 0.35/0.55  thf('78', plain,
% 0.35/0.55      (((~ (r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55         | ~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)
% 0.35/0.55         | ~ (v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)))
% 0.35/0.55         <= ((![X25 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X25))) & 
% 0.35/0.55             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.35/0.55  thf('79', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('80', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('81', plain,
% 0.35/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.35/0.55          | (v3_pre_topc @ (sk_D @ X24 @ X22 @ X23) @ X23)
% 0.35/0.55          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.35/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.55          | ~ (l1_pre_topc @ X23)
% 0.35/0.55          | ~ (v2_pre_topc @ X23)
% 0.35/0.55          | (v2_struct_0 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (v3_pre_topc @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.35/0.55  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('85', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (v3_pre_topc @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.35/0.55  thf('86', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['79', '85'])).
% 0.35/0.55  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('88', plain,
% 0.35/0.55      ((((v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.35/0.55  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('90', plain,
% 0.35/0.55      (((v3_pre_topc @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_A))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.35/0.55  thf('91', plain,
% 0.35/0.55      (((~ (r2_hidden @ sk_B @ (sk_D @ sk_C_1 @ sk_B @ sk_A))
% 0.35/0.55         | ~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)))
% 0.35/0.55         <= ((![X25 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X25))) & 
% 0.35/0.55             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['78', '90'])).
% 0.35/0.55  thf('92', plain,
% 0.35/0.55      ((~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))
% 0.35/0.55         <= ((![X25 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X25))) & 
% 0.35/0.55             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['75', '91'])).
% 0.35/0.55  thf('93', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('94', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('95', plain,
% 0.35/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.35/0.55          | (r1_tarski @ (sk_D @ X24 @ X22 @ X23) @ X24)
% 0.35/0.55          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.35/0.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.55          | ~ (l1_pre_topc @ X23)
% 0.35/0.55          | ~ (v2_pre_topc @ X23)
% 0.35/0.55          | (v2_struct_0 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.35/0.55  thf('96', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.35/0.55  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('99', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.35/0.55          | (r1_tarski @ (sk_D @ sk_C_1 @ X0 @ sk_A) @ sk_C_1)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.35/0.55  thf('100', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['93', '99'])).
% 0.35/0.55  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('102', plain,
% 0.35/0.55      ((((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.35/0.55  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('104', plain,
% 0.35/0.55      (((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('clc', [status(thm)], ['102', '103'])).
% 0.35/0.55  thf('105', plain,
% 0.35/0.55      (~
% 0.35/0.55       (![X25 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X25 @ sk_C_1)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X25))) | 
% 0.35/0.55       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['92', '104'])).
% 0.35/0.55  thf('106', plain, ($false),
% 0.35/0.55      inference('sat_resolution*', [status(thm)],
% 0.35/0.55                ['1', '3', '5', '42', '43', '105'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
