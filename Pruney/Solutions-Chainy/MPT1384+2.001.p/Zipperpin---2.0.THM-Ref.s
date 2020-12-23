%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NFKLWsdNCe

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:56 EST 2020

% Result     : Theorem 41.34s
% Output     : Refutation 41.45s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 482 expanded)
%              Number of leaves         :   25 ( 133 expanded)
%              Depth                    :   28
%              Number of atoms          : 1394 (8858 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t9_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( m1_connsp_2 @ D @ A @ C )
                              & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_connsp_2])).

thf('0',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
      | ~ ( r1_tarski @ X32 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
        | ~ ( r1_tarski @ X32 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_B )
   <= ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( m1_connsp_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_2 )
      | ~ ( r2_hidden @ sk_C_2 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_B )
   <= ( r2_hidden @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_2 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
        | ~ ( r1_tarski @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
        | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
          | ~ ( r1_tarski @ X32 @ sk_B ) )
      & ( r2_hidden @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_C_2 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X32 @ sk_A @ sk_C_2 )
          | ~ ( r1_tarski @ X32 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','29'])).

thf('31',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30'])).

thf('32',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('35',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30','53'])).

thf('55',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 ) ) ),
    inference(simpl_trail,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('57',plain,(
    ! [X31: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ X31 ) @ sk_A @ X31 )
      | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30','63'])).

thf('65',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('67',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

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

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_connsp_2 @ X27 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('88',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X31 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('93',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X31 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','30','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['86','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('101',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','102'])).

thf('104',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['38','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['32','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NFKLWsdNCe
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 41.34/41.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 41.34/41.62  % Solved by: fo/fo7.sh
% 41.34/41.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.34/41.62  % done 7754 iterations in 41.162s
% 41.34/41.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 41.34/41.62  % SZS output start Refutation
% 41.34/41.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 41.34/41.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 41.34/41.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 41.34/41.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 41.34/41.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 41.34/41.62  thf(sk_A_type, type, sk_A: $i).
% 41.34/41.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 41.34/41.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 41.34/41.62  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 41.34/41.62  thf(sk_B_type, type, sk_B: $i).
% 41.34/41.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 41.34/41.62  thf(sk_D_type, type, sk_D: $i > $i).
% 41.34/41.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 41.34/41.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 41.34/41.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 41.34/41.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 41.34/41.62  thf(t9_connsp_2, conjecture,
% 41.34/41.62    (![A:$i]:
% 41.34/41.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.34/41.62       ( ![B:$i]:
% 41.34/41.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62           ( ( v3_pre_topc @ B @ A ) <=>
% 41.34/41.62             ( ![C:$i]:
% 41.34/41.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 41.34/41.62                 ( ~( ( r2_hidden @ C @ B ) & 
% 41.34/41.62                      ( ![D:$i]:
% 41.34/41.62                        ( ( m1_subset_1 @
% 41.34/41.62                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 41.34/41.62                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 41.34/41.62  thf(zf_stmt_0, negated_conjecture,
% 41.34/41.62    (~( ![A:$i]:
% 41.34/41.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 41.34/41.62            ( l1_pre_topc @ A ) ) =>
% 41.34/41.62          ( ![B:$i]:
% 41.34/41.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62              ( ( v3_pre_topc @ B @ A ) <=>
% 41.34/41.62                ( ![C:$i]:
% 41.34/41.62                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 41.34/41.62                    ( ~( ( r2_hidden @ C @ B ) & 
% 41.34/41.62                         ( ![D:$i]:
% 41.34/41.62                           ( ( m1_subset_1 @
% 41.34/41.62                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 41.34/41.62                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 41.34/41.62    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 41.34/41.62  thf('0', plain,
% 41.34/41.62      (![X32 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62          | ~ (r1_tarski @ X32 @ sk_B)
% 41.34/41.62          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('1', plain,
% 41.34/41.62      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 41.34/41.62      inference('split', [status(esa)], ['0'])).
% 41.34/41.62  thf('2', plain,
% 41.34/41.62      ((![X32 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62           | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62           | ~ (r1_tarski @ X32 @ sk_B))) | 
% 41.34/41.62       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('split', [status(esa)], ['0'])).
% 41.34/41.62  thf('3', plain,
% 41.34/41.62      (((r2_hidden @ sk_C_2 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('4', plain,
% 41.34/41.62      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_2 @ sk_B))),
% 41.34/41.62      inference('split', [status(esa)], ['3'])).
% 41.34/41.62  thf('5', plain,
% 41.34/41.62      (((r2_hidden @ sk_C_2 @ sk_B)) <= (((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('split', [status(esa)], ['3'])).
% 41.34/41.62  thf('6', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf(t4_subset, axiom,
% 41.34/41.62    (![A:$i,B:$i,C:$i]:
% 41.34/41.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 41.34/41.62       ( m1_subset_1 @ A @ C ) ))).
% 41.34/41.62  thf('7', plain,
% 41.34/41.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 41.34/41.62         (~ (r2_hidden @ X15 @ X16)
% 41.34/41.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 41.34/41.62          | (m1_subset_1 @ X15 @ X17))),
% 41.34/41.62      inference('cnf', [status(esa)], [t4_subset])).
% 41.34/41.62  thf('8', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 41.34/41.62      inference('sup-', [status(thm)], ['6', '7'])).
% 41.34/41.62  thf('9', plain,
% 41.34/41.62      (((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62         <= (((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['5', '8'])).
% 41.34/41.62  thf('10', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (r1_tarski @ (sk_D @ X31) @ sk_B)
% 41.34/41.62          | (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('11', plain,
% 41.34/41.62      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 41.34/41.62      inference('split', [status(esa)], ['10'])).
% 41.34/41.62  thf('12', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf(t5_connsp_2, axiom,
% 41.34/41.62    (![A:$i]:
% 41.34/41.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.34/41.62       ( ![B:$i]:
% 41.34/41.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62           ( ![C:$i]:
% 41.34/41.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 41.34/41.62               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 41.34/41.62                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 41.34/41.62  thf('13', plain,
% 41.34/41.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 41.34/41.62          | ~ (v3_pre_topc @ X28 @ X29)
% 41.34/41.62          | ~ (r2_hidden @ X30 @ X28)
% 41.34/41.62          | (m1_connsp_2 @ X28 @ X29 @ X30)
% 41.34/41.62          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 41.34/41.62          | ~ (l1_pre_topc @ X29)
% 41.34/41.62          | ~ (v2_pre_topc @ X29)
% 41.34/41.62          | (v2_struct_0 @ X29))),
% 41.34/41.62      inference('cnf', [status(esa)], [t5_connsp_2])).
% 41.34/41.62  thf('14', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((v2_struct_0 @ sk_A)
% 41.34/41.62          | ~ (v2_pre_topc @ sk_A)
% 41.34/41.62          | ~ (l1_pre_topc @ sk_A)
% 41.34/41.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 41.34/41.62          | ~ (r2_hidden @ X0 @ sk_B)
% 41.34/41.62          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('sup-', [status(thm)], ['12', '13'])).
% 41.34/41.62  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('17', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((v2_struct_0 @ sk_A)
% 41.34/41.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 41.34/41.62          | ~ (r2_hidden @ X0 @ sk_B)
% 41.34/41.62          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('demod', [status(thm)], ['14', '15', '16'])).
% 41.34/41.62  thf('18', plain,
% 41.34/41.62      ((![X0 : $i]:
% 41.34/41.62          (~ (r2_hidden @ X0 @ sk_B)
% 41.34/41.62           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 41.34/41.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | (v2_struct_0 @ sk_A)))
% 41.34/41.62         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['11', '17'])).
% 41.34/41.62  thf('19', plain,
% 41.34/41.62      ((((v2_struct_0 @ sk_A)
% 41.34/41.62         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_2)
% 41.34/41.62         | ~ (r2_hidden @ sk_C_2 @ sk_B)))
% 41.34/41.62         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['9', '18'])).
% 41.34/41.62  thf('20', plain,
% 41.34/41.62      (((r2_hidden @ sk_C_2 @ sk_B)) <= (((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('split', [status(esa)], ['3'])).
% 41.34/41.62  thf('21', plain,
% 41.34/41.62      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_2)))
% 41.34/41.62         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('demod', [status(thm)], ['19', '20'])).
% 41.34/41.62  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('23', plain,
% 41.34/41.62      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_2))
% 41.34/41.62         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('clc', [status(thm)], ['21', '22'])).
% 41.34/41.62  thf('24', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('25', plain,
% 41.34/41.62      ((![X32 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62           | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62           | ~ (r1_tarski @ X32 @ sk_B)))
% 41.34/41.62         <= ((![X32 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62                 | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 41.34/41.62      inference('split', [status(esa)], ['0'])).
% 41.34/41.62  thf('26', plain,
% 41.34/41.62      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_2)))
% 41.34/41.62         <= ((![X32 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62                 | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62                 | ~ (r1_tarski @ X32 @ sk_B))))),
% 41.34/41.62      inference('sup-', [status(thm)], ['24', '25'])).
% 41.34/41.62  thf('27', plain,
% 41.34/41.62      ((~ (r1_tarski @ sk_B @ sk_B))
% 41.34/41.62         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 41.34/41.62             (![X32 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62                 | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62                 | ~ (r1_tarski @ X32 @ sk_B))) & 
% 41.34/41.62             ((r2_hidden @ sk_C_2 @ sk_B)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['23', '26'])).
% 41.34/41.62  thf(d10_xboole_0, axiom,
% 41.34/41.62    (![A:$i,B:$i]:
% 41.34/41.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 41.34/41.62  thf('28', plain,
% 41.34/41.62      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 41.34/41.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 41.34/41.62  thf('29', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 41.34/41.62      inference('simplify', [status(thm)], ['28'])).
% 41.34/41.62  thf('30', plain,
% 41.34/41.62      (~ ((r2_hidden @ sk_C_2 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 41.34/41.62       ~
% 41.34/41.62       (![X32 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62           | ~ (m1_connsp_2 @ X32 @ sk_A @ sk_C_2)
% 41.34/41.62           | ~ (r1_tarski @ X32 @ sk_B)))),
% 41.34/41.62      inference('demod', [status(thm)], ['27', '29'])).
% 41.34/41.62  thf('31', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('sat_resolution*', [status(thm)], ['2', '4', '30'])).
% 41.34/41.62  thf('32', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 41.34/41.62      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 41.34/41.62  thf('33', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf(fc9_tops_1, axiom,
% 41.34/41.62    (![A:$i,B:$i]:
% 41.34/41.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 41.34/41.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 41.34/41.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 41.34/41.62  thf('34', plain,
% 41.34/41.62      (![X18 : $i, X19 : $i]:
% 41.34/41.62         (~ (l1_pre_topc @ X18)
% 41.34/41.62          | ~ (v2_pre_topc @ X18)
% 41.34/41.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 41.34/41.62          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 41.34/41.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 41.34/41.62  thf('35', plain,
% 41.34/41.62      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 41.34/41.62        | ~ (v2_pre_topc @ sk_A)
% 41.34/41.62        | ~ (l1_pre_topc @ sk_A))),
% 41.34/41.62      inference('sup-', [status(thm)], ['33', '34'])).
% 41.34/41.62  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('38', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 41.34/41.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 41.34/41.62  thf('39', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf(t44_tops_1, axiom,
% 41.34/41.62    (![A:$i]:
% 41.34/41.62     ( ( l1_pre_topc @ A ) =>
% 41.34/41.62       ( ![B:$i]:
% 41.34/41.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 41.34/41.62  thf('40', plain,
% 41.34/41.62      (![X20 : $i, X21 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 41.34/41.62          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ X20)
% 41.34/41.62          | ~ (l1_pre_topc @ X21))),
% 41.34/41.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 41.34/41.62  thf('41', plain,
% 41.34/41.62      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 41.34/41.62      inference('sup-', [status(thm)], ['39', '40'])).
% 41.34/41.62  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('43', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 41.34/41.62      inference('demod', [status(thm)], ['41', '42'])).
% 41.34/41.62  thf('44', plain,
% 41.34/41.62      (![X4 : $i, X6 : $i]:
% 41.34/41.62         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 41.34/41.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 41.34/41.62  thf('45', plain,
% 41.34/41.62      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 41.34/41.62        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['43', '44'])).
% 41.34/41.62  thf(d3_tarski, axiom,
% 41.34/41.62    (![A:$i,B:$i]:
% 41.34/41.62     ( ( r1_tarski @ A @ B ) <=>
% 41.34/41.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 41.34/41.62  thf('46', plain,
% 41.34/41.62      (![X1 : $i, X3 : $i]:
% 41.34/41.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 41.34/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.34/41.62  thf('47', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 41.34/41.62      inference('sup-', [status(thm)], ['6', '7'])).
% 41.34/41.62  thf('48', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['46', '47'])).
% 41.34/41.62  thf('49', plain,
% 41.34/41.62      (![X1 : $i, X3 : $i]:
% 41.34/41.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 41.34/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.34/41.62  thf('50', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31)
% 41.34/41.62          | (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('51', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31)))
% 41.34/41.62         <= ((![X31 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62                 | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62                 | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31))))),
% 41.34/41.62      inference('split', [status(esa)], ['50'])).
% 41.34/41.62  thf('52', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31)
% 41.34/41.62          | (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('53', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31))) | 
% 41.34/41.62       ((v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('split', [status(esa)], ['52'])).
% 41.34/41.62  thf('54', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31)))),
% 41.34/41.62      inference('sat_resolution*', [status(thm)], ['2', '4', '30', '53'])).
% 41.34/41.62  thf('55', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31))),
% 41.34/41.62      inference('simpl_trail', [status(thm)], ['51', '54'])).
% 41.34/41.62  thf('56', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 41.34/41.62      inference('sup-', [status(thm)], ['6', '7'])).
% 41.34/41.62  thf('57', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         ((m1_connsp_2 @ (sk_D @ X31) @ sk_A @ X31)
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B))),
% 41.34/41.62      inference('clc', [status(thm)], ['55', '56'])).
% 41.34/41.62  thf('58', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 41.34/41.62             (sk_C @ X0 @ sk_B)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['49', '57'])).
% 41.34/41.62  thf('59', plain,
% 41.34/41.62      (![X1 : $i, X3 : $i]:
% 41.34/41.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 41.34/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.34/41.62  thf('60', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('61', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 41.34/41.62         <= ((![X31 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62                 | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62                 | (m1_subset_1 @ (sk_D @ X31) @ 
% 41.34/41.62                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 41.34/41.62      inference('split', [status(esa)], ['60'])).
% 41.34/41.62  thf('62', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | (v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('63', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 41.34/41.62       ((v3_pre_topc @ sk_B @ sk_A))),
% 41.34/41.62      inference('split', [status(esa)], ['62'])).
% 41.34/41.62  thf('64', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 41.34/41.62      inference('sat_resolution*', [status(thm)], ['2', '4', '30', '63'])).
% 41.34/41.62  thf('65', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62          | (m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.34/41.62      inference('simpl_trail', [status(thm)], ['61', '64'])).
% 41.34/41.62  thf('66', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 41.34/41.62      inference('sup-', [status(thm)], ['6', '7'])).
% 41.34/41.62  thf('67', plain,
% 41.34/41.62      (![X31 : $i]:
% 41.34/41.62         ((m1_subset_1 @ (sk_D @ X31) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | ~ (r2_hidden @ X31 @ sk_B))),
% 41.34/41.62      inference('clc', [status(thm)], ['65', '66'])).
% 41.34/41.62  thf('68', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 41.34/41.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.34/41.62      inference('sup-', [status(thm)], ['59', '67'])).
% 41.34/41.62  thf(d1_connsp_2, axiom,
% 41.34/41.62    (![A:$i]:
% 41.34/41.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 41.34/41.62       ( ![B:$i]:
% 41.34/41.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 41.34/41.62           ( ![C:$i]:
% 41.34/41.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 41.34/41.62                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 41.34/41.62  thf('69', plain,
% 41.34/41.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 41.34/41.62          | ~ (m1_connsp_2 @ X27 @ X26 @ X25)
% 41.34/41.62          | (r2_hidden @ X25 @ (k1_tops_1 @ X26 @ X27))
% 41.34/41.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 41.34/41.62          | ~ (l1_pre_topc @ X26)
% 41.34/41.62          | ~ (v2_pre_topc @ X26)
% 41.34/41.62          | (v2_struct_0 @ X26))),
% 41.34/41.62      inference('cnf', [status(esa)], [d1_connsp_2])).
% 41.34/41.62  thf('70', plain,
% 41.34/41.62      (![X0 : $i, X1 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (v2_struct_0 @ sk_A)
% 41.34/41.62          | ~ (v2_pre_topc @ sk_A)
% 41.34/41.62          | ~ (l1_pre_topc @ sk_A)
% 41.34/41.62          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 41.34/41.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['68', '69'])).
% 41.34/41.62  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('73', plain,
% 41.34/41.62      (![X0 : $i, X1 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (v2_struct_0 @ sk_A)
% 41.34/41.62          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 41.34/41.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('demod', [status(thm)], ['70', '71', '72'])).
% 41.34/41.62  thf('74', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | (v2_struct_0 @ sk_A)
% 41.34/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.34/41.62      inference('sup-', [status(thm)], ['58', '73'])).
% 41.34/41.62  thf('75', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((v2_struct_0 @ sk_A)
% 41.34/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 41.34/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.34/41.62      inference('simplify', [status(thm)], ['74'])).
% 41.34/41.62  thf('76', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | (v2_struct_0 @ sk_A))),
% 41.34/41.62      inference('sup-', [status(thm)], ['48', '75'])).
% 41.34/41.62  thf('77', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((v2_struct_0 @ sk_A)
% 41.34/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 41.34/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.34/41.62      inference('simplify', [status(thm)], ['76'])).
% 41.34/41.62  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('79', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))))),
% 41.34/41.62      inference('clc', [status(thm)], ['77', '78'])).
% 41.34/41.62  thf('80', plain,
% 41.34/41.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('81', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 41.34/41.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.34/41.62      inference('sup-', [status(thm)], ['59', '67'])).
% 41.34/41.62  thf(t48_tops_1, axiom,
% 41.34/41.62    (![A:$i]:
% 41.34/41.62     ( ( l1_pre_topc @ A ) =>
% 41.34/41.62       ( ![B:$i]:
% 41.34/41.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62           ( ![C:$i]:
% 41.34/41.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.34/41.62               ( ( r1_tarski @ B @ C ) =>
% 41.34/41.62                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 41.34/41.62  thf('82', plain,
% 41.34/41.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 41.34/41.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.34/41.62          | ~ (r1_tarski @ X22 @ X24)
% 41.34/41.62          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ (k1_tops_1 @ X23 @ X24))
% 41.34/41.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.34/41.62          | ~ (l1_pre_topc @ X23))),
% 41.34/41.62      inference('cnf', [status(esa)], [t48_tops_1])).
% 41.34/41.62  thf('83', plain,
% 41.34/41.62      (![X0 : $i, X1 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | ~ (l1_pre_topc @ sk_A)
% 41.34/41.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ X1))
% 41.34/41.62          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1))),
% 41.34/41.62      inference('sup-', [status(thm)], ['81', '82'])).
% 41.34/41.62  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 41.34/41.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.34/41.62  thf('85', plain,
% 41.34/41.62      (![X0 : $i, X1 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.34/41.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ X1))
% 41.34/41.62          | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1))),
% 41.34/41.62      inference('demod', [status(thm)], ['83', '84'])).
% 41.34/41.62  thf('86', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 41.34/41.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 41.34/41.62             (k1_tops_1 @ sk_A @ sk_B))
% 41.34/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.34/41.62      inference('sup-', [status(thm)], ['80', '85'])).
% 41.34/41.62  thf('87', plain,
% 41.34/41.62      (![X0 : $i]:
% 41.34/41.62         ((r1_tarski @ sk_B @ X0)
% 41.34/41.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 41.34/41.62      inference('sup-', [status(thm)], ['46', '47'])).
% 41.34/41.62  thf('88', plain,
% 41.34/41.62      ((![X31 : $i]:
% 41.34/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.34/41.62           | (r1_tarski @ (sk_D @ X31) @ sk_B)))
% 41.34/41.62         <= ((![X31 : $i]:
% 41.34/41.62                (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.34/41.62                 | ~ (r2_hidden @ X31 @ sk_B)
% 41.45/41.62                 | (r1_tarski @ (sk_D @ X31) @ sk_B))))),
% 41.45/41.62      inference('split', [status(esa)], ['10'])).
% 41.45/41.62  thf('89', plain,
% 41.45/41.62      ((![X0 : $i]:
% 41.45/41.62          ((r1_tarski @ sk_B @ X0)
% 41.45/41.62           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 41.45/41.62           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 41.45/41.62         <= ((![X31 : $i]:
% 41.45/41.62                (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.45/41.62                 | ~ (r2_hidden @ X31 @ sk_B)
% 41.45/41.62                 | (r1_tarski @ (sk_D @ X31) @ sk_B))))),
% 41.45/41.62      inference('sup-', [status(thm)], ['87', '88'])).
% 41.45/41.62  thf('90', plain,
% 41.45/41.62      (![X1 : $i, X3 : $i]:
% 41.45/41.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 41.45/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.45/41.62  thf('91', plain,
% 41.45/41.62      ((![X0 : $i]:
% 41.45/41.62          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 41.45/41.62           | (r1_tarski @ sk_B @ X0)))
% 41.45/41.62         <= ((![X31 : $i]:
% 41.45/41.62                (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.45/41.62                 | ~ (r2_hidden @ X31 @ sk_B)
% 41.45/41.62                 | (r1_tarski @ (sk_D @ X31) @ sk_B))))),
% 41.45/41.62      inference('clc', [status(thm)], ['89', '90'])).
% 41.45/41.62  thf('92', plain,
% 41.45/41.62      ((![X31 : $i]:
% 41.45/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.45/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.45/41.62           | (r1_tarski @ (sk_D @ X31) @ sk_B))) | 
% 41.45/41.62       ((v3_pre_topc @ sk_B @ sk_A))),
% 41.45/41.62      inference('split', [status(esa)], ['10'])).
% 41.45/41.62  thf('93', plain,
% 41.45/41.62      ((![X31 : $i]:
% 41.45/41.62          (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ sk_A))
% 41.45/41.62           | ~ (r2_hidden @ X31 @ sk_B)
% 41.45/41.62           | (r1_tarski @ (sk_D @ X31) @ sk_B)))),
% 41.45/41.62      inference('sat_resolution*', [status(thm)], ['2', '4', '30', '92'])).
% 41.45/41.62  thf('94', plain,
% 41.45/41.62      (![X0 : $i]:
% 41.45/41.62         ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 41.45/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.45/41.62      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 41.45/41.62  thf('95', plain,
% 41.45/41.62      (![X0 : $i]:
% 41.45/41.62         ((r1_tarski @ sk_B @ X0)
% 41.45/41.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 41.45/41.62             (k1_tops_1 @ sk_A @ sk_B)))),
% 41.45/41.62      inference('clc', [status(thm)], ['86', '94'])).
% 41.45/41.62  thf('96', plain,
% 41.45/41.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.45/41.62         (~ (r2_hidden @ X0 @ X1)
% 41.45/41.62          | (r2_hidden @ X0 @ X2)
% 41.45/41.62          | ~ (r1_tarski @ X1 @ X2))),
% 41.45/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.45/41.62  thf('97', plain,
% 41.45/41.62      (![X0 : $i, X1 : $i]:
% 41.45/41.62         ((r1_tarski @ sk_B @ X0)
% 41.45/41.62          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 41.45/41.62          | ~ (r2_hidden @ X1 @ 
% 41.45/41.62               (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B)))))),
% 41.45/41.62      inference('sup-', [status(thm)], ['95', '96'])).
% 41.45/41.62  thf('98', plain,
% 41.45/41.62      (![X0 : $i]:
% 41.45/41.62         ((r1_tarski @ sk_B @ X0)
% 41.45/41.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 41.45/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.45/41.62      inference('sup-', [status(thm)], ['79', '97'])).
% 41.45/41.62  thf('99', plain,
% 41.45/41.62      (![X0 : $i]:
% 41.45/41.62         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 41.45/41.62          | (r1_tarski @ sk_B @ X0))),
% 41.45/41.62      inference('simplify', [status(thm)], ['98'])).
% 41.45/41.62  thf('100', plain,
% 41.45/41.62      (![X1 : $i, X3 : $i]:
% 41.45/41.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 41.45/41.62      inference('cnf', [status(esa)], [d3_tarski])).
% 41.45/41.62  thf('101', plain,
% 41.45/41.62      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 41.45/41.62        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 41.45/41.62      inference('sup-', [status(thm)], ['99', '100'])).
% 41.45/41.62  thf('102', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 41.45/41.62      inference('simplify', [status(thm)], ['101'])).
% 41.45/41.62  thf('103', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 41.45/41.62      inference('demod', [status(thm)], ['45', '102'])).
% 41.45/41.62  thf('104', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 41.45/41.62      inference('demod', [status(thm)], ['38', '103'])).
% 41.45/41.62  thf('105', plain, ($false), inference('demod', [status(thm)], ['32', '104'])).
% 41.45/41.62  
% 41.45/41.62  % SZS output end Refutation
% 41.45/41.62  
% 41.45/41.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
