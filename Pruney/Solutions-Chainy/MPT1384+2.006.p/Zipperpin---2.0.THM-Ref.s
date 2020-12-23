%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Uk2uK8HlT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:57 EST 2020

% Result     : Theorem 27.15s
% Output     : Refutation 27.15s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 395 expanded)
%              Number of leaves         :   27 ( 120 expanded)
%              Depth                    :   24
%              Number of atoms          : 2208 (6612 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X33 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X33 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X32: $i] :
        ( ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 )
        | ~ ( r2_hidden @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X32 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,
    ( ! [X32: $i] :
        ( ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X32 @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

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

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('50',plain,
    ( ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 )
        | ~ ( r1_tarski @ sk_B @ X1 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ ( k1_tops_1 @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) )
   <= ! [X32: $i] :
        ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X32 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('83',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
      & ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['80','86'])).

thf('88',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X32 ) @ sk_A @ X32 ) )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ! [X32: $i] :
          ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X32 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X32 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('94',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('107',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('109',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ ( k1_tops_1 @ X27 @ X28 ) )
      | ( m1_connsp_2 @ X28 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','116'])).

thf('118',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('123',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('124',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('125',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('129',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X33 @ sk_B ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X33 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A @ sk_C_1 ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X33 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('133',plain,
    ( ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A @ sk_C_1 )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X33 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X33 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['122','133'])).

thf('135',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X33 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X33 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','89','91','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Uk2uK8HlT
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:51:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 27.15/27.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.15/27.36  % Solved by: fo/fo7.sh
% 27.15/27.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.15/27.36  % done 21014 iterations in 26.885s
% 27.15/27.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.15/27.36  % SZS output start Refutation
% 27.15/27.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.15/27.36  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 27.15/27.36  thf(sk_A_type, type, sk_A: $i).
% 27.15/27.36  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 27.15/27.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.15/27.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 27.15/27.36  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 27.15/27.36  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.15/27.36  thf(sk_C_1_type, type, sk_C_1: $i).
% 27.15/27.36  thf(sk_D_type, type, sk_D: $i > $i).
% 27.15/27.36  thf(sk_B_type, type, sk_B: $i).
% 27.15/27.36  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 27.15/27.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.15/27.36  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 27.15/27.36  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 27.15/27.36  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 27.15/27.36  thf(t9_connsp_2, conjecture,
% 27.15/27.36    (![A:$i]:
% 27.15/27.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.15/27.36       ( ![B:$i]:
% 27.15/27.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36           ( ( v3_pre_topc @ B @ A ) <=>
% 27.15/27.36             ( ![C:$i]:
% 27.15/27.36               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.15/27.36                 ( ~( ( r2_hidden @ C @ B ) & 
% 27.15/27.36                      ( ![D:$i]:
% 27.15/27.36                        ( ( m1_subset_1 @
% 27.15/27.36                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 27.15/27.36                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 27.15/27.36  thf(zf_stmt_0, negated_conjecture,
% 27.15/27.36    (~( ![A:$i]:
% 27.15/27.36        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 27.15/27.36            ( l1_pre_topc @ A ) ) =>
% 27.15/27.36          ( ![B:$i]:
% 27.15/27.36            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36              ( ( v3_pre_topc @ B @ A ) <=>
% 27.15/27.36                ( ![C:$i]:
% 27.15/27.36                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.15/27.36                    ( ~( ( r2_hidden @ C @ B ) & 
% 27.15/27.36                         ( ![D:$i]:
% 27.15/27.36                           ( ( m1_subset_1 @
% 27.15/27.36                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 27.15/27.36                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 27.15/27.36    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 27.15/27.36  thf('0', plain,
% 27.15/27.36      (![X33 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36          | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36          | ~ (r1_tarski @ X33 @ sk_B)
% 27.15/27.36          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('1', plain,
% 27.15/27.36      ((![X33 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36           | ~ (r1_tarski @ X33 @ sk_B))) | 
% 27.15/27.36       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('split', [status(esa)], ['0'])).
% 27.15/27.36  thf('2', plain,
% 27.15/27.36      (![X32 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36          | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36          | (r1_tarski @ (sk_D @ X32) @ sk_B)
% 27.15/27.36          | (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('3', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (r1_tarski @ (sk_D @ X32) @ sk_B))) | 
% 27.15/27.36       ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('split', [status(esa)], ['2'])).
% 27.15/27.36  thf('4', plain,
% 27.15/27.36      (![X32 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36          | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36          | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32)
% 27.15/27.36          | (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('5', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) | 
% 27.15/27.36       ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('split', [status(esa)], ['4'])).
% 27.15/27.36  thf('6', plain,
% 27.15/27.36      (![X32 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36          | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36          | (m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36          | (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('7', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 27.15/27.36       ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('split', [status(esa)], ['6'])).
% 27.15/27.36  thf(d3_tarski, axiom,
% 27.15/27.36    (![A:$i,B:$i]:
% 27.15/27.36     ( ( r1_tarski @ A @ B ) <=>
% 27.15/27.36       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 27.15/27.36  thf('8', plain,
% 27.15/27.36      (![X1 : $i, X3 : $i]:
% 27.15/27.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('9', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf(t3_subset, axiom,
% 27.15/27.36    (![A:$i,B:$i]:
% 27.15/27.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.15/27.36  thf('10', plain,
% 27.15/27.36      (![X10 : $i, X11 : $i]:
% 27.15/27.36         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 27.15/27.36      inference('cnf', [status(esa)], [t3_subset])).
% 27.15/27.36  thf('11', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['9', '10'])).
% 27.15/27.36  thf('12', plain,
% 27.15/27.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.15/27.36         (~ (r2_hidden @ X0 @ X1)
% 27.15/27.36          | (r2_hidden @ X0 @ X2)
% 27.15/27.36          | ~ (r1_tarski @ X1 @ X2))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('13', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 27.15/27.36      inference('sup-', [status(thm)], ['11', '12'])).
% 27.15/27.36  thf('14', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r1_tarski @ sk_B @ X0)
% 27.15/27.36          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['8', '13'])).
% 27.15/27.36  thf(d10_xboole_0, axiom,
% 27.15/27.36    (![A:$i,B:$i]:
% 27.15/27.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.15/27.36  thf('15', plain,
% 27.15/27.36      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 27.15/27.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.15/27.36  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 27.15/27.36      inference('simplify', [status(thm)], ['15'])).
% 27.15/27.36  thf('17', plain,
% 27.15/27.36      (![X10 : $i, X12 : $i]:
% 27.15/27.36         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 27.15/27.36      inference('cnf', [status(esa)], [t3_subset])).
% 27.15/27.36  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 27.15/27.36      inference('sup-', [status(thm)], ['16', '17'])).
% 27.15/27.36  thf(t4_subset, axiom,
% 27.15/27.36    (![A:$i,B:$i,C:$i]:
% 27.15/27.36     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 27.15/27.36       ( m1_subset_1 @ A @ C ) ))).
% 27.15/27.36  thf('19', plain,
% 27.15/27.36      (![X13 : $i, X14 : $i, X15 : $i]:
% 27.15/27.36         (~ (r2_hidden @ X13 @ X14)
% 27.15/27.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 27.15/27.36          | (m1_subset_1 @ X13 @ X15))),
% 27.15/27.36      inference('cnf', [status(esa)], [t4_subset])).
% 27.15/27.36  thf('20', plain,
% 27.15/27.36      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 27.15/27.36      inference('sup-', [status(thm)], ['18', '19'])).
% 27.15/27.36  thf('21', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r1_tarski @ sk_B @ X0)
% 27.15/27.36          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['14', '20'])).
% 27.15/27.36  thf('22', plain,
% 27.15/27.36      (![X1 : $i, X3 : $i]:
% 27.15/27.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('23', plain,
% 27.15/27.36      (![X32 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36          | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36          | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32)
% 27.15/27.36          | (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('24', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))))),
% 27.15/27.36      inference('split', [status(esa)], ['23'])).
% 27.15/27.36  thf('25', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('26', plain,
% 27.15/27.36      (![X13 : $i, X14 : $i, X15 : $i]:
% 27.15/27.36         (~ (r2_hidden @ X13 @ X14)
% 27.15/27.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 27.15/27.36          | (m1_subset_1 @ X13 @ X15))),
% 27.15/27.36      inference('cnf', [status(esa)], [t4_subset])).
% 27.15/27.36  thf('27', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 27.15/27.36      inference('sup-', [status(thm)], ['25', '26'])).
% 27.15/27.36  thf('28', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          ((m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32)
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))))),
% 27.15/27.36      inference('clc', [status(thm)], ['24', '27'])).
% 27.15/27.36  thf('29', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 27.15/27.36              (sk_C @ X0 @ sk_B))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['22', '28'])).
% 27.15/27.36  thf('30', plain,
% 27.15/27.36      (![X1 : $i, X3 : $i]:
% 27.15/27.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('31', plain,
% 27.15/27.36      (![X32 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36          | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36          | (m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36          | (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('32', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('split', [status(esa)], ['31'])).
% 27.15/27.36  thf('33', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 27.15/27.36      inference('sup-', [status(thm)], ['25', '26'])).
% 27.15/27.36  thf('34', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          ((m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('clc', [status(thm)], ['32', '33'])).
% 27.15/27.36  thf('35', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 27.15/27.36              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['30', '34'])).
% 27.15/27.36  thf(d1_connsp_2, axiom,
% 27.15/27.36    (![A:$i]:
% 27.15/27.36     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.15/27.36       ( ![B:$i]:
% 27.15/27.36         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 27.15/27.36           ( ![C:$i]:
% 27.15/27.36             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 27.15/27.36                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 27.15/27.36  thf('36', plain,
% 27.15/27.36      (![X26 : $i, X27 : $i, X28 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 27.15/27.36          | ~ (m1_connsp_2 @ X28 @ X27 @ X26)
% 27.15/27.36          | (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 27.15/27.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 27.15/27.36          | ~ (l1_pre_topc @ X27)
% 27.15/27.36          | ~ (v2_pre_topc @ X27)
% 27.15/27.36          | (v2_struct_0 @ X27))),
% 27.15/27.36      inference('cnf', [status(esa)], [d1_connsp_2])).
% 27.15/27.36  thf('37', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (v2_struct_0 @ sk_A)
% 27.15/27.36           | ~ (v2_pre_topc @ sk_A)
% 27.15/27.36           | ~ (l1_pre_topc @ sk_A)
% 27.15/27.36           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 27.15/27.36           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['35', '36'])).
% 27.15/27.36  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('40', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (v2_struct_0 @ sk_A)
% 27.15/27.36           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 27.15/27.36           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('demod', [status(thm)], ['37', '38', '39'])).
% 27.15/27.36  thf('41', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | (v2_struct_0 @ sk_A)
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['29', '40'])).
% 27.15/27.36  thf('42', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((v2_struct_0 @ sk_A)
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('simplify', [status(thm)], ['41'])).
% 27.15/27.36  thf('43', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | (v2_struct_0 @ sk_A)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['21', '42'])).
% 27.15/27.36  thf('44', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((v2_struct_0 @ sk_A)
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('simplify', [status(thm)], ['43'])).
% 27.15/27.36  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('46', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('clc', [status(thm)], ['44', '45'])).
% 27.15/27.36  thf('47', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('48', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['9', '10'])).
% 27.15/27.36  thf('49', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r1_tarski @ sk_B @ X0)
% 27.15/27.36          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['14', '20'])).
% 27.15/27.36  thf('50', plain,
% 27.15/27.36      ((![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (r1_tarski @ (sk_D @ X32) @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('split', [status(esa)], ['2'])).
% 27.15/27.36  thf('51', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 27.15/27.36           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['49', '50'])).
% 27.15/27.36  thf('52', plain,
% 27.15/27.36      (![X1 : $i, X3 : $i]:
% 27.15/27.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('53', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('clc', [status(thm)], ['51', '52'])).
% 27.15/27.36  thf(t1_xboole_1, axiom,
% 27.15/27.36    (![A:$i,B:$i,C:$i]:
% 27.15/27.36     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 27.15/27.36       ( r1_tarski @ A @ C ) ))).
% 27.15/27.36  thf('54', plain,
% 27.15/27.36      (![X7 : $i, X8 : $i, X9 : $i]:
% 27.15/27.36         (~ (r1_tarski @ X7 @ X8)
% 27.15/27.36          | ~ (r1_tarski @ X8 @ X9)
% 27.15/27.36          | (r1_tarski @ X7 @ X9))),
% 27.15/27.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.15/27.36  thf('55', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 27.15/27.36           | ~ (r1_tarski @ sk_B @ X1)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['53', '54'])).
% 27.15/27.36  thf('56', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['48', '55'])).
% 27.15/27.36  thf('57', plain,
% 27.15/27.36      (![X10 : $i, X12 : $i]:
% 27.15/27.36         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 27.15/27.36      inference('cnf', [status(esa)], [t3_subset])).
% 27.15/27.36  thf('58', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 27.15/27.36              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['56', '57'])).
% 27.15/27.36  thf(t48_tops_1, axiom,
% 27.15/27.36    (![A:$i]:
% 27.15/27.36     ( ( l1_pre_topc @ A ) =>
% 27.15/27.36       ( ![B:$i]:
% 27.15/27.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36           ( ![C:$i]:
% 27.15/27.36             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36               ( ( r1_tarski @ B @ C ) =>
% 27.15/27.36                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 27.15/27.36  thf('59', plain,
% 27.15/27.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 27.15/27.36          | ~ (r1_tarski @ X20 @ X22)
% 27.15/27.36          | (r1_tarski @ (k1_tops_1 @ X21 @ X20) @ (k1_tops_1 @ X21 @ X22))
% 27.15/27.36          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 27.15/27.36          | ~ (l1_pre_topc @ X21))),
% 27.15/27.36      inference('cnf', [status(esa)], [t48_tops_1])).
% 27.15/27.36  thf('60', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | ~ (l1_pre_topc @ sk_A)
% 27.15/27.36           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ X1))
% 27.15/27.36           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['58', '59'])).
% 27.15/27.36  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('62', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ X1))
% 27.15/27.36           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('demod', [status(thm)], ['60', '61'])).
% 27.15/27.36  thf('63', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 27.15/27.36           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['47', '62'])).
% 27.15/27.36  thf('64', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('clc', [status(thm)], ['51', '52'])).
% 27.15/27.36  thf('65', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 27.15/27.36              (k1_tops_1 @ sk_A @ sk_B))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('clc', [status(thm)], ['63', '64'])).
% 27.15/27.36  thf('66', plain,
% 27.15/27.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.15/27.36         (~ (r2_hidden @ X0 @ X1)
% 27.15/27.36          | (r2_hidden @ X0 @ X2)
% 27.15/27.36          | ~ (r1_tarski @ X1 @ X2))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('67', plain,
% 27.15/27.36      ((![X0 : $i, X1 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36           | ~ (r2_hidden @ X1 @ 
% 27.15/27.36                (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['65', '66'])).
% 27.15/27.36  thf('68', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['46', '67'])).
% 27.15/27.36  thf('69', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36           | (r1_tarski @ sk_B @ X0)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('simplify', [status(thm)], ['68'])).
% 27.15/27.36  thf('70', plain,
% 27.15/27.36      (![X1 : $i, X3 : $i]:
% 27.15/27.36         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 27.15/27.36      inference('cnf', [status(esa)], [d3_tarski])).
% 27.15/27.36  thf('71', plain,
% 27.15/27.36      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['69', '70'])).
% 27.15/27.36  thf('72', plain,
% 27.15/27.36      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('simplify', [status(thm)], ['71'])).
% 27.15/27.36  thf('73', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf(t44_tops_1, axiom,
% 27.15/27.36    (![A:$i]:
% 27.15/27.36     ( ( l1_pre_topc @ A ) =>
% 27.15/27.36       ( ![B:$i]:
% 27.15/27.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 27.15/27.36  thf('74', plain,
% 27.15/27.36      (![X18 : $i, X19 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 27.15/27.36          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 27.15/27.36          | ~ (l1_pre_topc @ X19))),
% 27.15/27.36      inference('cnf', [status(esa)], [t44_tops_1])).
% 27.15/27.36  thf('75', plain,
% 27.15/27.36      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 27.15/27.36      inference('sup-', [status(thm)], ['73', '74'])).
% 27.15/27.36  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('77', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 27.15/27.36      inference('demod', [status(thm)], ['75', '76'])).
% 27.15/27.36  thf('78', plain,
% 27.15/27.36      (![X4 : $i, X6 : $i]:
% 27.15/27.36         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 27.15/27.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.15/27.36  thf('79', plain,
% 27.15/27.36      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['77', '78'])).
% 27.15/27.36  thf('80', plain,
% 27.15/27.36      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['72', '79'])).
% 27.15/27.36  thf('81', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf(fc9_tops_1, axiom,
% 27.15/27.36    (![A:$i,B:$i]:
% 27.15/27.36     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 27.15/27.36         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.15/27.36       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 27.15/27.36  thf('82', plain,
% 27.15/27.36      (![X16 : $i, X17 : $i]:
% 27.15/27.36         (~ (l1_pre_topc @ X16)
% 27.15/27.36          | ~ (v2_pre_topc @ X16)
% 27.15/27.36          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 27.15/27.36          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 27.15/27.36      inference('cnf', [status(esa)], [fc9_tops_1])).
% 27.15/27.36  thf('83', plain,
% 27.15/27.36      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 27.15/27.36        | ~ (v2_pre_topc @ sk_A)
% 27.15/27.36        | ~ (l1_pre_topc @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['81', '82'])).
% 27.15/27.36  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('86', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 27.15/27.36      inference('demod', [status(thm)], ['83', '84', '85'])).
% 27.15/27.36  thf('87', plain,
% 27.15/27.36      (((v3_pre_topc @ sk_B @ sk_A))
% 27.15/27.36         <= ((![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (r1_tarski @ (sk_D @ X32) @ sk_B))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) & 
% 27.15/27.36             (![X32 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36                 | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36                 | (m1_subset_1 @ (sk_D @ X32) @ 
% 27.15/27.36                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 27.15/27.36      inference('sup+', [status(thm)], ['80', '86'])).
% 27.15/27.36  thf('88', plain,
% 27.15/27.36      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('split', [status(esa)], ['0'])).
% 27.15/27.36  thf('89', plain,
% 27.15/27.36      (~
% 27.15/27.36       (![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_connsp_2 @ (sk_D @ X32) @ sk_A @ X32))) | 
% 27.15/27.36       ~
% 27.15/27.36       (![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (m1_subset_1 @ (sk_D @ X32) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 27.15/27.36       ~
% 27.15/27.36       (![X32 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | ~ (r2_hidden @ X32 @ sk_B)
% 27.15/27.36           | (r1_tarski @ (sk_D @ X32) @ sk_B))) | 
% 27.15/27.36       ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['87', '88'])).
% 27.15/27.36  thf('90', plain,
% 27.15/27.36      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('91', plain,
% 27.15/27.36      (((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('split', [status(esa)], ['90'])).
% 27.15/27.36  thf('92', plain,
% 27.15/27.36      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('split', [status(esa)], ['90'])).
% 27.15/27.36  thf('93', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 27.15/27.36      inference('sup-', [status(thm)], ['11', '12'])).
% 27.15/27.36  thf('94', plain,
% 27.15/27.36      (((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['92', '93'])).
% 27.15/27.36  thf('95', plain,
% 27.15/27.36      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 27.15/27.36      inference('sup-', [status(thm)], ['18', '19'])).
% 27.15/27.36  thf('96', plain,
% 27.15/27.36      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['94', '95'])).
% 27.15/27.36  thf('97', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('98', plain,
% 27.15/27.36      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('split', [status(esa)], ['2'])).
% 27.15/27.36  thf('99', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf(t56_tops_1, axiom,
% 27.15/27.36    (![A:$i]:
% 27.15/27.36     ( ( l1_pre_topc @ A ) =>
% 27.15/27.36       ( ![B:$i]:
% 27.15/27.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36           ( ![C:$i]:
% 27.15/27.36             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.15/27.36               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 27.15/27.36                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 27.15/27.36  thf('100', plain,
% 27.15/27.36      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 27.15/27.36          | ~ (v3_pre_topc @ X23 @ X24)
% 27.15/27.36          | ~ (r1_tarski @ X23 @ X25)
% 27.15/27.36          | (r1_tarski @ X23 @ (k1_tops_1 @ X24 @ X25))
% 27.15/27.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 27.15/27.36          | ~ (l1_pre_topc @ X24))),
% 27.15/27.36      inference('cnf', [status(esa)], [t56_tops_1])).
% 27.15/27.36  thf('101', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         (~ (l1_pre_topc @ sk_A)
% 27.15/27.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 27.15/27.36          | ~ (r1_tarski @ sk_B @ X0)
% 27.15/27.36          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['99', '100'])).
% 27.15/27.36  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('103', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 27.15/27.36          | ~ (r1_tarski @ sk_B @ X0)
% 27.15/27.36          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 27.15/27.36      inference('demod', [status(thm)], ['101', '102'])).
% 27.15/27.36  thf('104', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          (~ (r1_tarski @ sk_B @ X0)
% 27.15/27.36           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 27.15/27.36           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['98', '103'])).
% 27.15/27.36  thf('105', plain,
% 27.15/27.36      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['97', '104'])).
% 27.15/27.36  thf('106', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 27.15/27.36      inference('simplify', [status(thm)], ['15'])).
% 27.15/27.36  thf('107', plain,
% 27.15/27.36      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('demod', [status(thm)], ['105', '106'])).
% 27.15/27.36  thf('108', plain,
% 27.15/27.36      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['77', '78'])).
% 27.15/27.36  thf('109', plain,
% 27.15/27.36      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['107', '108'])).
% 27.15/27.36  thf('110', plain,
% 27.15/27.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('111', plain,
% 27.15/27.36      (![X26 : $i, X27 : $i, X28 : $i]:
% 27.15/27.36         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 27.15/27.36          | ~ (r2_hidden @ X26 @ (k1_tops_1 @ X27 @ X28))
% 27.15/27.36          | (m1_connsp_2 @ X28 @ X27 @ X26)
% 27.15/27.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 27.15/27.36          | ~ (l1_pre_topc @ X27)
% 27.15/27.36          | ~ (v2_pre_topc @ X27)
% 27.15/27.36          | (v2_struct_0 @ X27))),
% 27.15/27.36      inference('cnf', [status(esa)], [d1_connsp_2])).
% 27.15/27.36  thf('112', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((v2_struct_0 @ sk_A)
% 27.15/27.36          | ~ (v2_pre_topc @ sk_A)
% 27.15/27.36          | ~ (l1_pre_topc @ sk_A)
% 27.15/27.36          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 27.15/27.36          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['110', '111'])).
% 27.15/27.36  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('115', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((v2_struct_0 @ sk_A)
% 27.15/27.36          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 27.15/27.36          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 27.15/27.36          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('demod', [status(thm)], ['112', '113', '114'])).
% 27.15/27.36  thf('116', plain,
% 27.15/27.36      ((![X0 : $i]:
% 27.15/27.36          (~ (r2_hidden @ X0 @ sk_B)
% 27.15/27.36           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.15/27.36           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 27.15/27.36           | (v2_struct_0 @ sk_A)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['109', '115'])).
% 27.15/27.36  thf('117', plain,
% 27.15/27.36      ((((v2_struct_0 @ sk_A)
% 27.15/27.36         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 27.15/27.36         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['96', '116'])).
% 27.15/27.36  thf('118', plain,
% 27.15/27.36      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('split', [status(esa)], ['90'])).
% 27.15/27.36  thf('119', plain,
% 27.15/27.36      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('demod', [status(thm)], ['117', '118'])).
% 27.15/27.36  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 27.15/27.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.15/27.36  thf('121', plain,
% 27.15/27.36      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 27.15/27.36      inference('clc', [status(thm)], ['119', '120'])).
% 27.15/27.36  thf('122', plain,
% 27.15/27.36      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['107', '108'])).
% 27.15/27.36  thf('123', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['9', '10'])).
% 27.15/27.36  thf('124', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 27.15/27.36      inference('demod', [status(thm)], ['75', '76'])).
% 27.15/27.36  thf('125', plain,
% 27.15/27.36      (![X7 : $i, X8 : $i, X9 : $i]:
% 27.15/27.36         (~ (r1_tarski @ X7 @ X8)
% 27.15/27.36          | ~ (r1_tarski @ X8 @ X9)
% 27.15/27.36          | (r1_tarski @ X7 @ X9))),
% 27.15/27.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.15/27.36  thf('126', plain,
% 27.15/27.36      (![X0 : $i]:
% 27.15/27.36         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 27.15/27.36          | ~ (r1_tarski @ sk_B @ X0))),
% 27.15/27.36      inference('sup-', [status(thm)], ['124', '125'])).
% 27.15/27.36  thf('127', plain,
% 27.15/27.36      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 27.15/27.36      inference('sup-', [status(thm)], ['123', '126'])).
% 27.15/27.36  thf('128', plain,
% 27.15/27.36      (![X10 : $i, X12 : $i]:
% 27.15/27.36         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 27.15/27.36      inference('cnf', [status(esa)], [t3_subset])).
% 27.15/27.36  thf('129', plain,
% 27.15/27.36      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 27.15/27.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['127', '128'])).
% 27.15/27.36  thf('130', plain,
% 27.15/27.36      ((![X33 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36           | ~ (r1_tarski @ X33 @ sk_B)))
% 27.15/27.36         <= ((![X33 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36                 | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36                 | ~ (r1_tarski @ X33 @ sk_B))))),
% 27.15/27.36      inference('split', [status(esa)], ['0'])).
% 27.15/27.36  thf('131', plain,
% 27.15/27.36      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 27.15/27.36         | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A @ sk_C_1)))
% 27.15/27.36         <= ((![X33 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36                 | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36                 | ~ (r1_tarski @ X33 @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['129', '130'])).
% 27.15/27.36  thf('132', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 27.15/27.36      inference('demod', [status(thm)], ['75', '76'])).
% 27.15/27.36  thf('133', plain,
% 27.15/27.36      ((~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A @ sk_C_1))
% 27.15/27.36         <= ((![X33 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36                 | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36                 | ~ (r1_tarski @ X33 @ sk_B))))),
% 27.15/27.36      inference('demod', [status(thm)], ['131', '132'])).
% 27.15/27.36  thf('134', plain,
% 27.15/27.36      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 27.15/27.36         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 27.15/27.36             (![X33 : $i]:
% 27.15/27.36                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36                 | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36                 | ~ (r1_tarski @ X33 @ sk_B))))),
% 27.15/27.36      inference('sup-', [status(thm)], ['122', '133'])).
% 27.15/27.36  thf('135', plain,
% 27.15/27.36      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 27.15/27.36       ~
% 27.15/27.36       (![X33 : $i]:
% 27.15/27.36          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.15/27.36           | ~ (m1_connsp_2 @ X33 @ sk_A @ sk_C_1)
% 27.15/27.36           | ~ (r1_tarski @ X33 @ sk_B)))),
% 27.15/27.36      inference('sup-', [status(thm)], ['121', '134'])).
% 27.15/27.36  thf('136', plain, ($false),
% 27.15/27.36      inference('sat_resolution*', [status(thm)],
% 27.15/27.36                ['1', '3', '5', '7', '89', '91', '135'])).
% 27.15/27.36  
% 27.15/27.36  % SZS output end Refutation
% 27.15/27.36  
% 27.15/27.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
