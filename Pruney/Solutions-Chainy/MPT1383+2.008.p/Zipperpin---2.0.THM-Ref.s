%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OTnBxDK7WB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 212 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          : 1297 (4076 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
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
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X24 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X24 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X24 ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X24 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X24 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X8 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('29',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X24 ) ) ),
    inference(demod,[status(thm)],['26','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X24 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','33'])).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ( ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X24 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ( m1_connsp_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_D )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ sk_D )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
        | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) )
        | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('77',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('94',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','40','42','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OTnBxDK7WB
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 178 iterations in 0.087s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.35/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
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
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (((r1_tarski @ sk_D @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (((r1_tarski @ sk_D @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.35/0.55       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X24 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55          | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55          | ~ (r2_hidden @ sk_B @ X24)
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((![X24 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X24))) | 
% 0.35/0.55       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['6'])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
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
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.55          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.35/0.55          | (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.55          | ~ (l1_pre_topc @ X16)
% 0.35/0.55          | ~ (v2_pre_topc @ X16)
% 0.35/0.55          | (v2_struct_0 @ X16))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['8', '14'])).
% 0.35/0.55  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.55         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('clc', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_k1_tops_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55       ( m1_subset_1 @
% 0.35/0.55         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X6)
% 0.35/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.35/0.55          | (m1_subset_1 @ (k1_tops_1 @ X6 @ X7) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X6))))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      ((![X24 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X24)))
% 0.35/0.55         <= ((![X24 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X24))))),
% 0.35/0.55      inference('split', [status(esa)], ['6'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.35/0.55         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.35/0.55         <= ((![X24 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X24))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(fc9_tops_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (![X8 : $i, X9 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X8)
% 0.35/0.55          | ~ (v2_pre_topc @ X8)
% 0.35/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.35/0.55          | (v3_pre_topc @ (k1_tops_1 @ X8 @ X9) @ X8))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('32', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.35/0.55         <= ((![X24 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X24))))),
% 0.35/0.55      inference('demod', [status(thm)], ['26', '32'])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.35/0.55         <= ((![X24 : $i]:
% 0.35/0.55                (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55                 | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55                 | ~ (r2_hidden @ sk_B @ X24))) & 
% 0.35/0.55             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['19', '33'])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t44_tops_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (![X10 : $i, X11 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.55          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ X10)
% 0.35/0.55          | ~ (l1_pre_topc @ X11))),
% 0.35/0.55      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('39', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (~
% 0.35/0.55       (![X24 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.35/0.55           | ~ (r1_tarski @ X24 @ sk_C)
% 0.35/0.55           | ~ (r2_hidden @ sk_B @ X24))) | 
% 0.35/0.55       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['34', '39'])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('split', [status(esa)], ['41'])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('44', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['41'])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf(t5_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.35/0.55                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.35/0.55          | ~ (v3_pre_topc @ X21 @ X22)
% 0.35/0.55          | ~ (r2_hidden @ X23 @ X21)
% 0.35/0.55          | (m1_connsp_2 @ X21 @ X22 @ X23)
% 0.35/0.55          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.35/0.55          | ~ (l1_pre_topc @ X22)
% 0.35/0.55          | ~ (v2_pre_topc @ X22)
% 0.35/0.55          | (v2_struct_0 @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.35/0.55           | ~ (r2_hidden @ X0 @ sk_D)
% 0.35/0.55           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.35/0.55           | ~ (r2_hidden @ X0 @ sk_D)
% 0.35/0.55           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (r2_hidden @ X0 @ sk_D)
% 0.35/0.55           | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55           | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['45', '51'])).
% 0.35/0.55  thf('53', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A)
% 0.35/0.55         | (m1_connsp_2 @ sk_D @ sk_A @ sk_B)
% 0.35/0.55         | ~ (r2_hidden @ sk_B @ sk_D)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['44', '52'])).
% 0.35/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (((~ (r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_D @ sk_A @ sk_B)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_D @ sk_A @ sk_B))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['43', '55'])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.55          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.35/0.55          | (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.55          | ~ (l1_pre_topc @ X16)
% 0.35/0.55          | ~ (v2_pre_topc @ X16)
% 0.35/0.55          | (v2_struct_0 @ X16))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.35/0.55           | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.55  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((v2_struct_0 @ sk_A)
% 0.35/0.55           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))
% 0.35/0.55           | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D))
% 0.35/0.55         | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['56', '62'])).
% 0.35/0.55  thf('64', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)) | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.35/0.55  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('clc', [status(thm)], ['65', '66'])).
% 0.35/0.55  thf('68', plain,
% 0.35/0.55      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.35/0.55      inference('split', [status(esa)], ['2'])).
% 0.35/0.55  thf('69', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('split', [status(esa)], ['4'])).
% 0.35/0.55  thf(t48_tops_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ( r1_tarski @ B @ C ) =>
% 0.35/0.55                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('71', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.55          | ~ (r1_tarski @ X12 @ X14)
% 0.35/0.55          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ (k1_tops_1 @ X13 @ X14))
% 0.35/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.55          | ~ (l1_pre_topc @ X13))),
% 0.35/0.55      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.35/0.55  thf('72', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (l1_pre_topc @ sk_A)
% 0.35/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.55           | ~ (r1_tarski @ sk_D @ X0)))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.35/0.55  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('74', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.55           | ~ (r1_tarski @ sk_D @ X0)))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.35/0.55  thf('75', plain,
% 0.35/0.55      (((~ (r1_tarski @ sk_D @ sk_C)
% 0.35/0.55         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.55         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['69', '74'])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.55         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['68', '75'])).
% 0.35/0.55  thf(t3_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.55  thf('77', plain,
% 0.35/0.55      (![X3 : $i, X5 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('78', plain,
% 0.35/0.55      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.55         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.35/0.55  thf(l3_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.55  thf('79', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.55          | (r2_hidden @ X0 @ X2)
% 0.35/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.35/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.55  thf('80', plain,
% 0.35/0.55      ((![X0 : $i]:
% 0.35/0.55          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 0.35/0.55         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.35/0.55  thf('81', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['67', '80'])).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('83', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.55          | ~ (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.35/0.55          | (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.55          | ~ (l1_pre_topc @ X16)
% 0.35/0.55          | ~ (v2_pre_topc @ X16)
% 0.35/0.55          | (v2_struct_0 @ X16))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.55  thf('84', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.35/0.55  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('87', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.35/0.55  thf('88', plain,
% 0.35/0.55      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.55         | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['81', '87'])).
% 0.35/0.55  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('90', plain,
% 0.35/0.55      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.35/0.55  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('92', plain,
% 0.35/0.55      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.55         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.35/0.55             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.35/0.55             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.35/0.55             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.55      inference('clc', [status(thm)], ['90', '91'])).
% 0.35/0.55  thf('93', plain,
% 0.35/0.55      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.55         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.55      inference('split', [status(esa)], ['6'])).
% 0.35/0.55  thf('94', plain,
% 0.35/0.55      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.35/0.55       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.35/0.55       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.35/0.55       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.35/0.55  thf('95', plain, ($false),
% 0.35/0.55      inference('sat_resolution*', [status(thm)],
% 0.35/0.55                ['1', '3', '5', '7', '40', '42', '94'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
