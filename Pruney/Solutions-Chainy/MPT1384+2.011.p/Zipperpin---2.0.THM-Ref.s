%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fnPXw0lbOz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:58 EST 2020

% Result     : Theorem 10.03s
% Output     : Refutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 659 expanded)
%              Number of leaves         :   27 ( 184 expanded)
%              Depth                    :   28
%              Number of atoms          : 1759 (11013 expanded)
%              Number of equality atoms :    5 (  36 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
      | ~ ( r1_tarski @ X38 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X32 )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ( m1_connsp_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
      | ~ ( r2_hidden @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('35',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C )
          | ~ ( r1_tarski @ X38 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','36'])).

thf('38',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('41',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X20 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('54',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ sk_B ) @ X0 )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('64',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','36','67'])).

thf('69',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simpl_trail,[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X37: $i] :
      ( ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ~ ( r2_hidden @ X37 @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('74',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','36','77'])).

thf('79',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('81',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X37 @ sk_B ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','81'])).

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

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ X0 )
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
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('95',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('96',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('97',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','36','96'])).

thf('98',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('100',plain,(
    ! [X37: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B )
      | ~ ( r2_hidden @ X37 @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','81'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('118',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('122',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','123'])).

thf('125',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['44','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['38','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fnPXw0lbOz
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 10.03/10.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.03/10.31  % Solved by: fo/fo7.sh
% 10.03/10.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.03/10.31  % done 11516 iterations in 9.857s
% 10.03/10.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.03/10.31  % SZS output start Refutation
% 10.03/10.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.03/10.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 10.03/10.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.03/10.31  thf(sk_A_type, type, sk_A: $i).
% 10.03/10.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 10.03/10.31  thf(sk_B_type, type, sk_B: $i).
% 10.03/10.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.03/10.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.03/10.31  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 10.03/10.31  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 10.03/10.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.03/10.31  thf(sk_C_type, type, sk_C: $i).
% 10.03/10.31  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 10.03/10.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.03/10.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.03/10.31  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.03/10.31  thf(t9_connsp_2, conjecture,
% 10.03/10.31    (![A:$i]:
% 10.03/10.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.03/10.31       ( ![B:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31           ( ( v3_pre_topc @ B @ A ) <=>
% 10.03/10.31             ( ![C:$i]:
% 10.03/10.31               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.03/10.31                 ( ~( ( r2_hidden @ C @ B ) & 
% 10.03/10.31                      ( ![D:$i]:
% 10.03/10.31                        ( ( m1_subset_1 @
% 10.03/10.31                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 10.03/10.31                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 10.03/10.31  thf(zf_stmt_0, negated_conjecture,
% 10.03/10.31    (~( ![A:$i]:
% 10.03/10.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.03/10.31            ( l1_pre_topc @ A ) ) =>
% 10.03/10.31          ( ![B:$i]:
% 10.03/10.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31              ( ( v3_pre_topc @ B @ A ) <=>
% 10.03/10.31                ( ![C:$i]:
% 10.03/10.31                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.03/10.31                    ( ~( ( r2_hidden @ C @ B ) & 
% 10.03/10.31                         ( ![D:$i]:
% 10.03/10.31                           ( ( m1_subset_1 @
% 10.03/10.31                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 10.03/10.31                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 10.03/10.31    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 10.03/10.31  thf('0', plain,
% 10.03/10.31      (![X38 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31          | ~ (r1_tarski @ X38 @ sk_B)
% 10.03/10.31          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('1', plain,
% 10.03/10.31      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 10.03/10.31      inference('split', [status(esa)], ['0'])).
% 10.03/10.31  thf('2', plain,
% 10.03/10.31      ((![X38 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31           | ~ (r1_tarski @ X38 @ sk_B))) | 
% 10.03/10.31       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('split', [status(esa)], ['0'])).
% 10.03/10.31  thf('3', plain,
% 10.03/10.31      (((r2_hidden @ sk_C @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('4', plain,
% 10.03/10.31      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C @ sk_B))),
% 10.03/10.31      inference('split', [status(esa)], ['3'])).
% 10.03/10.31  thf('5', plain,
% 10.03/10.31      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('split', [status(esa)], ['3'])).
% 10.03/10.31  thf('6', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf(l3_subset_1, axiom,
% 10.03/10.31    (![A:$i,B:$i]:
% 10.03/10.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.03/10.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 10.03/10.31  thf('7', plain,
% 10.03/10.31      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.03/10.31         (~ (r2_hidden @ X3 @ X4)
% 10.03/10.31          | (r2_hidden @ X3 @ X5)
% 10.03/10.31          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 10.03/10.31      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.03/10.31  thf('8', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['6', '7'])).
% 10.03/10.31  thf('9', plain,
% 10.03/10.31      (((r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))
% 10.03/10.31         <= (((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['5', '8'])).
% 10.03/10.31  thf(d10_xboole_0, axiom,
% 10.03/10.31    (![A:$i,B:$i]:
% 10.03/10.31     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.03/10.31  thf('10', plain,
% 10.03/10.31      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 10.03/10.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.03/10.31  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.03/10.31      inference('simplify', [status(thm)], ['10'])).
% 10.03/10.31  thf(t3_subset, axiom,
% 10.03/10.31    (![A:$i,B:$i]:
% 10.03/10.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.03/10.31  thf('12', plain,
% 10.03/10.31      (![X9 : $i, X11 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 10.03/10.31      inference('cnf', [status(esa)], [t3_subset])).
% 10.03/10.31  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.31      inference('sup-', [status(thm)], ['11', '12'])).
% 10.03/10.31  thf(t4_subset, axiom,
% 10.03/10.31    (![A:$i,B:$i,C:$i]:
% 10.03/10.31     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 10.03/10.31       ( m1_subset_1 @ A @ C ) ))).
% 10.03/10.31  thf('14', plain,
% 10.03/10.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.03/10.31         (~ (r2_hidden @ X12 @ X13)
% 10.03/10.31          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 10.03/10.31          | (m1_subset_1 @ X12 @ X14))),
% 10.03/10.31      inference('cnf', [status(esa)], [t4_subset])).
% 10.03/10.31  thf('15', plain,
% 10.03/10.31      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 10.03/10.31      inference('sup-', [status(thm)], ['13', '14'])).
% 10.03/10.31  thf('16', plain,
% 10.03/10.31      (((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 10.03/10.31         <= (((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['9', '15'])).
% 10.03/10.31  thf('17', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)
% 10.03/10.31          | (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('18', plain,
% 10.03/10.31      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 10.03/10.31      inference('split', [status(esa)], ['17'])).
% 10.03/10.31  thf('19', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf(t5_connsp_2, axiom,
% 10.03/10.31    (![A:$i]:
% 10.03/10.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.03/10.31       ( ![B:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31           ( ![C:$i]:
% 10.03/10.31             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.03/10.31               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 10.03/10.31                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 10.03/10.31  thf('20', plain,
% 10.03/10.31      (![X31 : $i, X32 : $i, X33 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 10.03/10.31          | ~ (v3_pre_topc @ X31 @ X32)
% 10.03/10.31          | ~ (r2_hidden @ X33 @ X31)
% 10.03/10.31          | (m1_connsp_2 @ X31 @ X32 @ X33)
% 10.03/10.31          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 10.03/10.31          | ~ (l1_pre_topc @ X32)
% 10.03/10.31          | ~ (v2_pre_topc @ X32)
% 10.03/10.31          | (v2_struct_0 @ X32))),
% 10.03/10.31      inference('cnf', [status(esa)], [t5_connsp_2])).
% 10.03/10.31  thf('21', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((v2_struct_0 @ sk_A)
% 10.03/10.31          | ~ (v2_pre_topc @ sk_A)
% 10.03/10.31          | ~ (l1_pre_topc @ sk_A)
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 10.03/10.31          | ~ (r2_hidden @ X0 @ sk_B)
% 10.03/10.31          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('sup-', [status(thm)], ['19', '20'])).
% 10.03/10.31  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('24', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((v2_struct_0 @ sk_A)
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 10.03/10.31          | ~ (r2_hidden @ X0 @ sk_B)
% 10.03/10.31          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('demod', [status(thm)], ['21', '22', '23'])).
% 10.03/10.31  thf('25', plain,
% 10.03/10.31      ((![X0 : $i]:
% 10.03/10.31          (~ (r2_hidden @ X0 @ sk_B)
% 10.03/10.31           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 10.03/10.31           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | (v2_struct_0 @ sk_A)))
% 10.03/10.31         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['18', '24'])).
% 10.03/10.31  thf('26', plain,
% 10.03/10.31      ((((v2_struct_0 @ sk_A)
% 10.03/10.31         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)
% 10.03/10.31         | ~ (r2_hidden @ sk_C @ sk_B)))
% 10.03/10.31         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['16', '25'])).
% 10.03/10.31  thf('27', plain,
% 10.03/10.31      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('split', [status(esa)], ['3'])).
% 10.03/10.31  thf('28', plain,
% 10.03/10.31      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)))
% 10.03/10.31         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('demod', [status(thm)], ['26', '27'])).
% 10.03/10.31  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('30', plain,
% 10.03/10.31      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C))
% 10.03/10.31         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 10.03/10.31      inference('clc', [status(thm)], ['28', '29'])).
% 10.03/10.31  thf('31', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('32', plain,
% 10.03/10.31      ((![X38 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31           | ~ (r1_tarski @ X38 @ sk_B)))
% 10.03/10.31         <= ((![X38 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 10.03/10.31      inference('split', [status(esa)], ['0'])).
% 10.03/10.31  thf('33', plain,
% 10.03/10.31      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C)))
% 10.03/10.31         <= ((![X38 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 10.03/10.31      inference('sup-', [status(thm)], ['31', '32'])).
% 10.03/10.31  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 10.03/10.31      inference('simplify', [status(thm)], ['10'])).
% 10.03/10.31  thf('35', plain,
% 10.03/10.31      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C))
% 10.03/10.31         <= ((![X38 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 10.03/10.31      inference('demod', [status(thm)], ['33', '34'])).
% 10.03/10.31  thf('36', plain,
% 10.03/10.31      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 10.03/10.31       ~
% 10.03/10.31       (![X38 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C)
% 10.03/10.31           | ~ (r1_tarski @ X38 @ sk_B))) | 
% 10.03/10.31       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('sup-', [status(thm)], ['30', '35'])).
% 10.03/10.31  thf('37', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('sat_resolution*', [status(thm)], ['2', '4', '36'])).
% 10.03/10.31  thf('38', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 10.03/10.31      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 10.03/10.31  thf('39', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf(fc9_tops_1, axiom,
% 10.03/10.31    (![A:$i,B:$i]:
% 10.03/10.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 10.03/10.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.03/10.31       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 10.03/10.31  thf('40', plain,
% 10.03/10.31      (![X17 : $i, X18 : $i]:
% 10.03/10.31         (~ (l1_pre_topc @ X17)
% 10.03/10.31          | ~ (v2_pre_topc @ X17)
% 10.03/10.31          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.03/10.31          | (v3_pre_topc @ (k1_tops_1 @ X17 @ X18) @ X17))),
% 10.03/10.31      inference('cnf', [status(esa)], [fc9_tops_1])).
% 10.03/10.31  thf('41', plain,
% 10.03/10.31      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 10.03/10.31        | ~ (v2_pre_topc @ sk_A)
% 10.03/10.31        | ~ (l1_pre_topc @ sk_A))),
% 10.03/10.31      inference('sup-', [status(thm)], ['39', '40'])).
% 10.03/10.31  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('44', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 10.03/10.31      inference('demod', [status(thm)], ['41', '42', '43'])).
% 10.03/10.31  thf('45', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf(t44_tops_1, axiom,
% 10.03/10.31    (![A:$i]:
% 10.03/10.31     ( ( l1_pre_topc @ A ) =>
% 10.03/10.31       ( ![B:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 10.03/10.31  thf('46', plain,
% 10.03/10.31      (![X19 : $i, X20 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 10.03/10.31          | (r1_tarski @ (k1_tops_1 @ X20 @ X19) @ X19)
% 10.03/10.31          | ~ (l1_pre_topc @ X20))),
% 10.03/10.31      inference('cnf', [status(esa)], [t44_tops_1])).
% 10.03/10.31  thf('47', plain,
% 10.03/10.31      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['45', '46'])).
% 10.03/10.31  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('49', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 10.03/10.31      inference('demod', [status(thm)], ['47', '48'])).
% 10.03/10.31  thf('50', plain,
% 10.03/10.31      (![X0 : $i, X2 : $i]:
% 10.03/10.31         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.03/10.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.03/10.31  thf('51', plain,
% 10.03/10.31      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['49', '50'])).
% 10.03/10.31  thf('52', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.31      inference('sup-', [status(thm)], ['11', '12'])).
% 10.03/10.31  thf('53', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 10.03/10.31      inference('demod', [status(thm)], ['47', '48'])).
% 10.03/10.31  thf('54', plain,
% 10.03/10.31      (![X9 : $i, X11 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 10.03/10.31      inference('cnf', [status(esa)], [t3_subset])).
% 10.03/10.31  thf('55', plain,
% 10.03/10.31      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['53', '54'])).
% 10.03/10.31  thf(t7_subset_1, axiom,
% 10.03/10.31    (![A:$i,B:$i]:
% 10.03/10.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.03/10.31       ( ![C:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.03/10.31           ( ( ![D:$i]:
% 10.03/10.31               ( ( m1_subset_1 @ D @ A ) =>
% 10.03/10.31                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 10.03/10.31             ( r1_tarski @ B @ C ) ) ) ) ))).
% 10.03/10.31  thf('56', plain,
% 10.03/10.31      (![X6 : $i, X7 : $i, X8 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 10.03/10.31          | (r1_tarski @ X8 @ X6)
% 10.03/10.31          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 10.03/10.31          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 10.03/10.31      inference('cnf', [status(esa)], [t7_subset_1])).
% 10.03/10.31  thf('57', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 10.03/10.31          | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ sk_B) @ X0)
% 10.03/10.31          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['55', '56'])).
% 10.03/10.31  thf('58', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['52', '57'])).
% 10.03/10.31  thf('59', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('60', plain,
% 10.03/10.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.03/10.31         (~ (r2_hidden @ X12 @ X13)
% 10.03/10.31          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 10.03/10.31          | (m1_subset_1 @ X12 @ X14))),
% 10.03/10.31      inference('cnf', [status(esa)], [t4_subset])).
% 10.03/10.31  thf('61', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['59', '60'])).
% 10.03/10.31  thf('62', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['58', '61'])).
% 10.03/10.31  thf('63', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['52', '57'])).
% 10.03/10.31  thf('64', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 10.03/10.31          | (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('65', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)))
% 10.03/10.31         <= ((![X37 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31                 | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31                 | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))))),
% 10.03/10.31      inference('split', [status(esa)], ['64'])).
% 10.03/10.31  thf('66', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 10.03/10.31          | (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('67', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))) | 
% 10.03/10.31       ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('split', [status(esa)], ['66'])).
% 10.03/10.31  thf('68', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)))),
% 10.03/10.31      inference('sat_resolution*', [status(thm)], ['2', '4', '36', '67'])).
% 10.03/10.31  thf('69', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))),
% 10.03/10.31      inference('simpl_trail', [status(thm)], ['65', '68'])).
% 10.03/10.31  thf('70', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['59', '60'])).
% 10.03/10.31  thf('71', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         ((m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B))),
% 10.03/10.31      inference('clc', [status(thm)], ['69', '70'])).
% 10.03/10.31  thf('72', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (m1_connsp_2 @ 
% 10.03/10.31           (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 10.03/10.31           sk_A @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['63', '71'])).
% 10.03/10.31  thf('73', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['52', '57'])).
% 10.03/10.31  thf('74', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('75', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 10.03/10.31         <= ((![X37 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31                 | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31                 | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 10.03/10.31      inference('split', [status(esa)], ['74'])).
% 10.03/10.31  thf('76', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | (v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('77', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 10.03/10.31       ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('split', [status(esa)], ['76'])).
% 10.03/10.31  thf('78', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 10.03/10.31      inference('sat_resolution*', [status(thm)], ['2', '4', '36', '77'])).
% 10.03/10.31  thf('79', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 10.03/10.31             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.03/10.31      inference('simpl_trail', [status(thm)], ['75', '78'])).
% 10.03/10.31  thf('80', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['59', '60'])).
% 10.03/10.31  thf('81', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         ((m1_subset_1 @ (sk_D_1 @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B))),
% 10.03/10.31      inference('clc', [status(thm)], ['79', '80'])).
% 10.03/10.31  thf('82', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (m1_subset_1 @ 
% 10.03/10.31           (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 10.03/10.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.03/10.31      inference('sup-', [status(thm)], ['73', '81'])).
% 10.03/10.31  thf(d1_connsp_2, axiom,
% 10.03/10.31    (![A:$i]:
% 10.03/10.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.03/10.31       ( ![B:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.03/10.31           ( ![C:$i]:
% 10.03/10.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 10.03/10.31                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 10.03/10.31  thf('83', plain,
% 10.03/10.31      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 10.03/10.31          | ~ (m1_connsp_2 @ X30 @ X29 @ X28)
% 10.03/10.31          | (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 10.03/10.31          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 10.03/10.31          | ~ (l1_pre_topc @ X29)
% 10.03/10.31          | ~ (v2_pre_topc @ X29)
% 10.03/10.31          | (v2_struct_0 @ X29))),
% 10.03/10.31      inference('cnf', [status(esa)], [d1_connsp_2])).
% 10.03/10.31  thf('84', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | (v2_struct_0 @ sk_A)
% 10.03/10.31          | ~ (v2_pre_topc @ sk_A)
% 10.03/10.31          | ~ (l1_pre_topc @ sk_A)
% 10.03/10.31          | (r2_hidden @ X0 @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ 
% 10.03/10.31              (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31          | ~ (m1_connsp_2 @ 
% 10.03/10.31               (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 10.03/10.31               sk_A @ X0)
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['82', '83'])).
% 10.03/10.31  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('87', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | (v2_struct_0 @ sk_A)
% 10.03/10.31          | (r2_hidden @ X0 @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ 
% 10.03/10.31              (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31          | ~ (m1_connsp_2 @ 
% 10.03/10.31               (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 10.03/10.31               sk_A @ X0)
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('demod', [status(thm)], ['84', '85', '86'])).
% 10.03/10.31  thf('88', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | ~ (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31             (u1_struct_0 @ sk_A))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31        | (v2_struct_0 @ sk_A)
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['72', '87'])).
% 10.03/10.31  thf('89', plain,
% 10.03/10.31      (((v2_struct_0 @ sk_A)
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31        | ~ (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31             (u1_struct_0 @ sk_A))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('simplify', [status(thm)], ['88'])).
% 10.03/10.31  thf('90', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31        | (v2_struct_0 @ sk_A))),
% 10.03/10.31      inference('sup-', [status(thm)], ['62', '89'])).
% 10.03/10.31  thf('91', plain,
% 10.03/10.31      (((v2_struct_0 @ sk_A)
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('simplify', [status(thm)], ['90'])).
% 10.03/10.31  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('93', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))))),
% 10.03/10.31      inference('clc', [status(thm)], ['91', '92'])).
% 10.03/10.31  thf('94', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['52', '57'])).
% 10.03/10.31  thf('95', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)))
% 10.03/10.31         <= ((![X37 : $i]:
% 10.03/10.31                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31                 | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31                 | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))))),
% 10.03/10.31      inference('split', [status(esa)], ['17'])).
% 10.03/10.31  thf('96', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))) | 
% 10.03/10.31       ((v3_pre_topc @ sk_B @ sk_A))),
% 10.03/10.31      inference('split', [status(esa)], ['17'])).
% 10.03/10.31  thf('97', plain,
% 10.03/10.31      ((![X37 : $i]:
% 10.03/10.31          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31           | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)))),
% 10.03/10.31      inference('sat_resolution*', [status(thm)], ['2', '4', '36', '96'])).
% 10.03/10.31  thf('98', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 10.03/10.31          | ~ (r2_hidden @ X37 @ sk_B)
% 10.03/10.31          | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))),
% 10.03/10.31      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 10.03/10.31  thf('99', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['59', '60'])).
% 10.03/10.31  thf('100', plain,
% 10.03/10.31      (![X37 : $i]:
% 10.03/10.31         ((r1_tarski @ (sk_D_1 @ X37) @ sk_B) | ~ (r2_hidden @ X37 @ sk_B))),
% 10.03/10.31      inference('clc', [status(thm)], ['98', '99'])).
% 10.03/10.31  thf('101', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ 
% 10.03/10.31           (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['94', '100'])).
% 10.03/10.31  thf('102', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (m1_subset_1 @ 
% 10.03/10.31           (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 10.03/10.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.03/10.31      inference('sup-', [status(thm)], ['73', '81'])).
% 10.03/10.31  thf(t48_tops_1, axiom,
% 10.03/10.31    (![A:$i]:
% 10.03/10.31     ( ( l1_pre_topc @ A ) =>
% 10.03/10.31       ( ![B:$i]:
% 10.03/10.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31           ( ![C:$i]:
% 10.03/10.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.03/10.31               ( ( r1_tarski @ B @ C ) =>
% 10.03/10.31                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 10.03/10.31  thf('103', plain,
% 10.03/10.31      (![X21 : $i, X22 : $i, X23 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.03/10.31          | ~ (r1_tarski @ X21 @ X23)
% 10.03/10.31          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ (k1_tops_1 @ X22 @ X23))
% 10.03/10.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.03/10.31          | ~ (l1_pre_topc @ X22))),
% 10.03/10.31      inference('cnf', [status(esa)], [t48_tops_1])).
% 10.03/10.31  thf('104', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | ~ (l1_pre_topc @ sk_A)
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | (r1_tarski @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ 
% 10.03/10.31              (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ X0))
% 10.03/10.31          | ~ (r1_tarski @ 
% 10.03/10.31               (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ X0))),
% 10.03/10.31      inference('sup-', [status(thm)], ['102', '103'])).
% 10.03/10.31  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('106', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31          | (r1_tarski @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ 
% 10.03/10.31              (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31             (k1_tops_1 @ sk_A @ X0))
% 10.03/10.31          | ~ (r1_tarski @ 
% 10.03/10.31               (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ X0))),
% 10.03/10.31      inference('demod', [status(thm)], ['104', '105'])).
% 10.03/10.31  thf('107', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['101', '106'])).
% 10.03/10.31  thf('108', plain,
% 10.03/10.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.03/10.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.31  thf('109', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('demod', [status(thm)], ['107', '108'])).
% 10.03/10.31  thf('110', plain,
% 10.03/10.31      (((r1_tarski @ 
% 10.03/10.31         (k1_tops_1 @ sk_A @ 
% 10.03/10.31          (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31         (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('simplify', [status(thm)], ['109'])).
% 10.03/10.31  thf('111', plain,
% 10.03/10.31      (![X9 : $i, X11 : $i]:
% 10.03/10.31         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 10.03/10.31      inference('cnf', [status(esa)], [t3_subset])).
% 10.03/10.31  thf('112', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (m1_subset_1 @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ 
% 10.03/10.31            (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 10.03/10.31           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 10.03/10.31      inference('sup-', [status(thm)], ['110', '111'])).
% 10.03/10.31  thf('113', plain,
% 10.03/10.31      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.03/10.31         (~ (r2_hidden @ X3 @ X4)
% 10.03/10.31          | (r2_hidden @ X3 @ X5)
% 10.03/10.31          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 10.03/10.31      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.03/10.31  thf('114', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | ~ (r2_hidden @ X0 @ 
% 10.03/10.31               (k1_tops_1 @ sk_A @ 
% 10.03/10.31                (sk_D_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))))),
% 10.03/10.31      inference('sup-', [status(thm)], ['112', '113'])).
% 10.03/10.31  thf('115', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31           (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['93', '114'])).
% 10.03/10.31  thf('116', plain,
% 10.03/10.31      (((r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 10.03/10.31         (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('simplify', [status(thm)], ['115'])).
% 10.03/10.31  thf('117', plain,
% 10.03/10.31      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 10.03/10.31      inference('sup-', [status(thm)], ['53', '54'])).
% 10.03/10.31  thf('118', plain,
% 10.03/10.31      (![X6 : $i, X7 : $i, X8 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 10.03/10.31          | (r1_tarski @ X8 @ X6)
% 10.03/10.31          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 10.03/10.31          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 10.03/10.31      inference('cnf', [status(esa)], [t7_subset_1])).
% 10.03/10.31  thf('119', plain,
% 10.03/10.31      (![X0 : $i]:
% 10.03/10.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 10.03/10.31          | ~ (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ sk_B) @ 
% 10.03/10.31               (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['117', '118'])).
% 10.03/10.31  thf('120', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))),
% 10.03/10.31      inference('sup-', [status(thm)], ['116', '119'])).
% 10.03/10.31  thf('121', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.31      inference('sup-', [status(thm)], ['11', '12'])).
% 10.03/10.31  thf('122', plain,
% 10.03/10.31      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 10.03/10.31        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.03/10.31      inference('demod', [status(thm)], ['120', '121'])).
% 10.03/10.31  thf('123', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 10.03/10.31      inference('simplify', [status(thm)], ['122'])).
% 10.03/10.31  thf('124', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 10.03/10.31      inference('demod', [status(thm)], ['51', '123'])).
% 10.03/10.31  thf('125', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 10.03/10.31      inference('demod', [status(thm)], ['44', '124'])).
% 10.03/10.31  thf('126', plain, ($false), inference('demod', [status(thm)], ['38', '125'])).
% 10.03/10.31  
% 10.03/10.31  % SZS output end Refutation
% 10.03/10.31  
% 10.14/10.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
