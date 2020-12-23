%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLV4r2BOG0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:56 EST 2020

% Result     : Theorem 7.55s
% Output     : Refutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  192 (1123 expanded)
%              Number of leaves         :   28 ( 325 expanded)
%              Depth                    :   26
%              Number of atoms          : 2810 (19495 expanded)
%              Number of equality atoms :   21 (  62 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
      | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X38 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
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
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) ) ),
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
    ( ! [X37: $i] :
        ( ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 )
        | ~ ( r2_hidden @ X37 @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,
    ( ! [X37: $i] :
        ( ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X37 @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_connsp_2 @ X27 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
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
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ( m1_connsp_2 @ X27 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('96',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('107',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','110'])).

thf('112',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('113',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('114',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('117',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 )
        | ( ( k1_tops_1 @ X24 @ X23 )
         != X23 )
        | ( v3_pre_topc @ X23 @ X24 ) )
    | ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(split,[status(esa)],['116'])).

thf('122',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 ) ) ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != X23 )
      | ( v3_pre_topc @ X23 @ X24 ) ) ),
    inference(simpl_trail,[status(thm)],['114','122'])).

thf('124',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['112','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','127'])).

thf('129',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','110'])).

thf('130',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','110'])).

thf('131',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['72','110'])).

thf('132',plain,
    ( ( ( sk_B != sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
      & ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,
    ( ~ ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X37 ) @ sk_A @ X37 ) )
    | ~ ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X37 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X37 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('138',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['136'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('140',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('142',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('144',plain,(
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

thf('145',plain,(
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

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','150'])).

thf('152',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['136'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('160',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','135','137','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BLV4r2BOG0
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.55/7.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.55/7.80  % Solved by: fo/fo7.sh
% 7.55/7.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.55/7.80  % done 7619 iterations in 7.347s
% 7.55/7.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.55/7.80  % SZS output start Refutation
% 7.55/7.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.55/7.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.55/7.80  thf(sk_D_type, type, sk_D: $i > $i).
% 7.55/7.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.55/7.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.55/7.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.55/7.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.55/7.80  thf(sk_B_type, type, sk_B: $i).
% 7.55/7.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.55/7.80  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 7.55/7.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.55/7.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.55/7.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.55/7.80  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.55/7.80  thf(sk_A_type, type, sk_A: $i).
% 7.55/7.80  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.55/7.80  thf(t9_connsp_2, conjecture,
% 7.55/7.80    (![A:$i]:
% 7.55/7.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.55/7.80       ( ![B:$i]:
% 7.55/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80           ( ( v3_pre_topc @ B @ A ) <=>
% 7.55/7.80             ( ![C:$i]:
% 7.55/7.80               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 7.55/7.80                 ( ~( ( r2_hidden @ C @ B ) & 
% 7.55/7.80                      ( ![D:$i]:
% 7.55/7.80                        ( ( m1_subset_1 @
% 7.55/7.80                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 7.55/7.80                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.55/7.80  thf(zf_stmt_0, negated_conjecture,
% 7.55/7.80    (~( ![A:$i]:
% 7.55/7.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.55/7.80            ( l1_pre_topc @ A ) ) =>
% 7.55/7.80          ( ![B:$i]:
% 7.55/7.80            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80              ( ( v3_pre_topc @ B @ A ) <=>
% 7.55/7.80                ( ![C:$i]:
% 7.55/7.80                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 7.55/7.80                    ( ~( ( r2_hidden @ C @ B ) & 
% 7.55/7.80                         ( ![D:$i]:
% 7.55/7.80                           ( ( m1_subset_1 @
% 7.55/7.80                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 7.55/7.80                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.55/7.80    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 7.55/7.80  thf('0', plain,
% 7.55/7.80      (![X38 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80          | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.80          | ~ (r1_tarski @ X38 @ sk_B)
% 7.55/7.80          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('1', plain,
% 7.55/7.80      ((![X38 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.80           | ~ (r1_tarski @ X38 @ sk_B))) | 
% 7.55/7.80       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('split', [status(esa)], ['0'])).
% 7.55/7.80  thf('2', plain,
% 7.55/7.80      (![X37 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80          | (r1_tarski @ (sk_D @ X37) @ sk_B)
% 7.55/7.80          | (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('3', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (r1_tarski @ (sk_D @ X37) @ sk_B))) | 
% 7.55/7.80       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('split', [status(esa)], ['2'])).
% 7.55/7.80  thf('4', plain,
% 7.55/7.80      (![X37 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80          | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37)
% 7.55/7.80          | (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('5', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) | 
% 7.55/7.80       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('split', [status(esa)], ['4'])).
% 7.55/7.80  thf('6', plain,
% 7.55/7.80      (![X37 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80          | (m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80          | (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('7', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 7.55/7.80       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('split', [status(esa)], ['6'])).
% 7.55/7.80  thf(d3_tarski, axiom,
% 7.55/7.80    (![A:$i,B:$i]:
% 7.55/7.80     ( ( r1_tarski @ A @ B ) <=>
% 7.55/7.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.55/7.80  thf('8', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('9', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf(t3_subset, axiom,
% 7.55/7.80    (![A:$i,B:$i]:
% 7.55/7.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.55/7.80  thf('10', plain,
% 7.55/7.80      (![X10 : $i, X11 : $i]:
% 7.55/7.80         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.55/7.80      inference('cnf', [status(esa)], [t3_subset])).
% 7.55/7.80  thf('11', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 7.55/7.80      inference('sup-', [status(thm)], ['9', '10'])).
% 7.55/7.80  thf('12', plain,
% 7.55/7.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.55/7.80         (~ (r2_hidden @ X0 @ X1)
% 7.55/7.80          | (r2_hidden @ X0 @ X2)
% 7.55/7.80          | ~ (r1_tarski @ X1 @ X2))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('13', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 7.55/7.80      inference('sup-', [status(thm)], ['11', '12'])).
% 7.55/7.80  thf('14', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ sk_B @ X0)
% 7.55/7.80          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['8', '13'])).
% 7.55/7.80  thf(d10_xboole_0, axiom,
% 7.55/7.80    (![A:$i,B:$i]:
% 7.55/7.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.55/7.80  thf('15', plain,
% 7.55/7.80      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 7.55/7.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.55/7.80  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 7.55/7.80      inference('simplify', [status(thm)], ['15'])).
% 7.55/7.80  thf('17', plain,
% 7.55/7.80      (![X10 : $i, X12 : $i]:
% 7.55/7.80         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 7.55/7.80      inference('cnf', [status(esa)], [t3_subset])).
% 7.55/7.80  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.55/7.80      inference('sup-', [status(thm)], ['16', '17'])).
% 7.55/7.80  thf(t4_subset, axiom,
% 7.55/7.80    (![A:$i,B:$i,C:$i]:
% 7.55/7.80     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 7.55/7.80       ( m1_subset_1 @ A @ C ) ))).
% 7.55/7.80  thf('19', plain,
% 7.55/7.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.55/7.80         (~ (r2_hidden @ X13 @ X14)
% 7.55/7.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 7.55/7.80          | (m1_subset_1 @ X13 @ X15))),
% 7.55/7.80      inference('cnf', [status(esa)], [t4_subset])).
% 7.55/7.80  thf('20', plain,
% 7.55/7.80      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 7.55/7.80      inference('sup-', [status(thm)], ['18', '19'])).
% 7.55/7.80  thf('21', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ sk_B @ X0)
% 7.55/7.80          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['14', '20'])).
% 7.55/7.80  thf('22', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('23', plain,
% 7.55/7.80      (![X37 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80          | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37)
% 7.55/7.80          | (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('24', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))))),
% 7.55/7.80      inference('split', [status(esa)], ['23'])).
% 7.55/7.80  thf('25', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('26', plain,
% 7.55/7.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.55/7.80         (~ (r2_hidden @ X13 @ X14)
% 7.55/7.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 7.55/7.80          | (m1_subset_1 @ X13 @ X15))),
% 7.55/7.80      inference('cnf', [status(esa)], [t4_subset])).
% 7.55/7.80  thf('27', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 7.55/7.80      inference('sup-', [status(thm)], ['25', '26'])).
% 7.55/7.80  thf('28', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          ((m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37)
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))))),
% 7.55/7.80      inference('clc', [status(thm)], ['24', '27'])).
% 7.55/7.80  thf('29', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 7.55/7.80              (sk_C @ X0 @ sk_B))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['22', '28'])).
% 7.55/7.80  thf('30', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('31', plain,
% 7.55/7.80      (![X37 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80          | (m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80          | (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('32', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('split', [status(esa)], ['31'])).
% 7.55/7.80  thf('33', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 7.55/7.80      inference('sup-', [status(thm)], ['25', '26'])).
% 7.55/7.80  thf('34', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          ((m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('clc', [status(thm)], ['32', '33'])).
% 7.55/7.80  thf('35', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 7.55/7.80              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['30', '34'])).
% 7.55/7.80  thf(d1_connsp_2, axiom,
% 7.55/7.80    (![A:$i]:
% 7.55/7.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.55/7.80       ( ![B:$i]:
% 7.55/7.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 7.55/7.80           ( ![C:$i]:
% 7.55/7.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 7.55/7.80                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.55/7.80  thf('36', plain,
% 7.55/7.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 7.55/7.80          | ~ (m1_connsp_2 @ X27 @ X26 @ X25)
% 7.55/7.80          | (r2_hidden @ X25 @ (k1_tops_1 @ X26 @ X27))
% 7.55/7.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 7.55/7.80          | ~ (l1_pre_topc @ X26)
% 7.55/7.80          | ~ (v2_pre_topc @ X26)
% 7.55/7.80          | (v2_struct_0 @ X26))),
% 7.55/7.80      inference('cnf', [status(esa)], [d1_connsp_2])).
% 7.55/7.80  thf('37', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (v2_struct_0 @ sk_A)
% 7.55/7.80           | ~ (v2_pre_topc @ sk_A)
% 7.55/7.80           | ~ (l1_pre_topc @ sk_A)
% 7.55/7.80           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 7.55/7.80           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['35', '36'])).
% 7.55/7.80  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('40', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (v2_struct_0 @ sk_A)
% 7.55/7.80           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 7.55/7.80           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('demod', [status(thm)], ['37', '38', '39'])).
% 7.55/7.80  thf('41', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | (v2_struct_0 @ sk_A)
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['29', '40'])).
% 7.55/7.80  thf('42', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((v2_struct_0 @ sk_A)
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('simplify', [status(thm)], ['41'])).
% 7.55/7.80  thf('43', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | (v2_struct_0 @ sk_A)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['21', '42'])).
% 7.55/7.80  thf('44', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((v2_struct_0 @ sk_A)
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('simplify', [status(thm)], ['43'])).
% 7.55/7.80  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('46', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('clc', [status(thm)], ['44', '45'])).
% 7.55/7.80  thf('47', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('48', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 7.55/7.80      inference('sup-', [status(thm)], ['9', '10'])).
% 7.55/7.80  thf('49', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ sk_B @ X0)
% 7.55/7.80          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['14', '20'])).
% 7.55/7.80  thf('50', plain,
% 7.55/7.80      ((![X37 : $i]:
% 7.55/7.80          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80           | (r1_tarski @ (sk_D @ X37) @ sk_B)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('split', [status(esa)], ['2'])).
% 7.55/7.80  thf('51', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 7.55/7.80           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['49', '50'])).
% 7.55/7.80  thf('52', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('53', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('clc', [status(thm)], ['51', '52'])).
% 7.55/7.80  thf(t1_xboole_1, axiom,
% 7.55/7.80    (![A:$i,B:$i,C:$i]:
% 7.55/7.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 7.55/7.80       ( r1_tarski @ A @ C ) ))).
% 7.55/7.80  thf('54', plain,
% 7.55/7.80      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.55/7.80         (~ (r1_tarski @ X7 @ X8)
% 7.55/7.80          | ~ (r1_tarski @ X8 @ X9)
% 7.55/7.80          | (r1_tarski @ X7 @ X9))),
% 7.55/7.80      inference('cnf', [status(esa)], [t1_xboole_1])).
% 7.55/7.80  thf('55', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)
% 7.55/7.80           | ~ (r1_tarski @ sk_B @ X1)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['53', '54'])).
% 7.55/7.80  thf('56', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ (u1_struct_0 @ sk_A))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['48', '55'])).
% 7.55/7.80  thf('57', plain,
% 7.55/7.80      (![X10 : $i, X12 : $i]:
% 7.55/7.80         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 7.55/7.80      inference('cnf', [status(esa)], [t3_subset])).
% 7.55/7.80  thf('58', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 7.55/7.80              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['56', '57'])).
% 7.55/7.80  thf(t48_tops_1, axiom,
% 7.55/7.80    (![A:$i]:
% 7.55/7.80     ( ( l1_pre_topc @ A ) =>
% 7.55/7.80       ( ![B:$i]:
% 7.55/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80           ( ![C:$i]:
% 7.55/7.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80               ( ( r1_tarski @ B @ C ) =>
% 7.55/7.80                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.55/7.80  thf('59', plain,
% 7.55/7.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.55/7.80          | ~ (r1_tarski @ X18 @ X20)
% 7.55/7.80          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 7.55/7.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.55/7.80          | ~ (l1_pre_topc @ X19))),
% 7.55/7.80      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.55/7.80  thf('60', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | ~ (l1_pre_topc @ sk_A)
% 7.55/7.80           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ X1))
% 7.55/7.80           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['58', '59'])).
% 7.55/7.80  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('62', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ X1))
% 7.55/7.80           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('demod', [status(thm)], ['60', '61'])).
% 7.55/7.80  thf('63', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 7.55/7.80           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['47', '62'])).
% 7.55/7.80  thf('64', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('clc', [status(thm)], ['51', '52'])).
% 7.55/7.80  thf('65', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 7.55/7.80              (k1_tops_1 @ sk_A @ sk_B))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('clc', [status(thm)], ['63', '64'])).
% 7.55/7.80  thf('66', plain,
% 7.55/7.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.55/7.80         (~ (r2_hidden @ X0 @ X1)
% 7.55/7.80          | (r2_hidden @ X0 @ X2)
% 7.55/7.80          | ~ (r1_tarski @ X1 @ X2))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('67', plain,
% 7.55/7.80      ((![X0 : $i, X1 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80           | ~ (r2_hidden @ X1 @ 
% 7.55/7.80                (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['65', '66'])).
% 7.55/7.80  thf('68', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r1_tarski @ sk_B @ X0)
% 7.55/7.80           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['46', '67'])).
% 7.55/7.80  thf('69', plain,
% 7.55/7.80      ((![X0 : $i]:
% 7.55/7.80          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80           | (r1_tarski @ sk_B @ X0)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('simplify', [status(thm)], ['68'])).
% 7.55/7.80  thf('70', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('71', plain,
% 7.55/7.80      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('sup-', [status(thm)], ['69', '70'])).
% 7.55/7.80  thf('72', plain,
% 7.55/7.80      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.80         <= ((![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.80             (![X37 : $i]:
% 7.55/7.80                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.80                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.80                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.80                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.80      inference('simplify', [status(thm)], ['71'])).
% 7.55/7.80  thf('73', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('74', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf(dt_k1_tops_1, axiom,
% 7.55/7.80    (![A:$i,B:$i]:
% 7.55/7.80     ( ( ( l1_pre_topc @ A ) & 
% 7.55/7.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.55/7.80       ( m1_subset_1 @
% 7.55/7.80         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.55/7.80  thf('75', plain,
% 7.55/7.80      (![X16 : $i, X17 : $i]:
% 7.55/7.80         (~ (l1_pre_topc @ X16)
% 7.55/7.80          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 7.55/7.80          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 7.55/7.80             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 7.55/7.80      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.55/7.80  thf('76', plain,
% 7.55/7.80      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.55/7.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.80        | ~ (l1_pre_topc @ sk_A))),
% 7.55/7.80      inference('sup-', [status(thm)], ['74', '75'])).
% 7.55/7.80  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('78', plain,
% 7.55/7.80      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.55/7.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('demod', [status(thm)], ['76', '77'])).
% 7.55/7.80  thf('79', plain,
% 7.55/7.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.55/7.80         (~ (r2_hidden @ X13 @ X14)
% 7.55/7.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 7.55/7.80          | (m1_subset_1 @ X13 @ X15))),
% 7.55/7.80      inference('cnf', [status(esa)], [t4_subset])).
% 7.55/7.80  thf('80', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['78', '79'])).
% 7.55/7.80  thf('81', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.55/7.80             (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['73', '80'])).
% 7.55/7.80  thf('82', plain,
% 7.55/7.80      (![X1 : $i, X3 : $i]:
% 7.55/7.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.55/7.80      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.80  thf('83', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('84', plain,
% 7.55/7.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 7.55/7.80          | ~ (r2_hidden @ X25 @ (k1_tops_1 @ X26 @ X27))
% 7.55/7.80          | (m1_connsp_2 @ X27 @ X26 @ X25)
% 7.55/7.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 7.55/7.80          | ~ (l1_pre_topc @ X26)
% 7.55/7.80          | ~ (v2_pre_topc @ X26)
% 7.55/7.80          | (v2_struct_0 @ X26))),
% 7.55/7.80      inference('cnf', [status(esa)], [d1_connsp_2])).
% 7.55/7.80  thf('85', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((v2_struct_0 @ sk_A)
% 7.55/7.80          | ~ (v2_pre_topc @ sk_A)
% 7.55/7.80          | ~ (l1_pre_topc @ sk_A)
% 7.55/7.80          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 7.55/7.80          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['83', '84'])).
% 7.55/7.80  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('88', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((v2_struct_0 @ sk_A)
% 7.55/7.80          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 7.55/7.80          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('demod', [status(thm)], ['85', '86', '87'])).
% 7.55/7.80  thf('89', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.55/7.80               (u1_struct_0 @ sk_A))
% 7.55/7.80          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 7.55/7.80             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.80          | (v2_struct_0 @ sk_A))),
% 7.55/7.80      inference('sup-', [status(thm)], ['82', '88'])).
% 7.55/7.80  thf('90', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | (v2_struct_0 @ sk_A)
% 7.55/7.80          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 7.55/7.80             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.55/7.80      inference('sup-', [status(thm)], ['81', '89'])).
% 7.55/7.80  thf('91', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((m1_connsp_2 @ sk_B @ sk_A @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.80          | (v2_struct_0 @ sk_A)
% 7.55/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.55/7.80      inference('simplify', [status(thm)], ['90'])).
% 7.55/7.80  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('93', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 7.55/7.80             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.55/7.80      inference('clc', [status(thm)], ['91', '92'])).
% 7.55/7.80  thf('94', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.55/7.80             (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('sup-', [status(thm)], ['73', '80'])).
% 7.55/7.80  thf('95', plain,
% 7.55/7.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf(t6_connsp_2, axiom,
% 7.55/7.80    (![A:$i]:
% 7.55/7.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.55/7.80       ( ![B:$i]:
% 7.55/7.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.80           ( ![C:$i]:
% 7.55/7.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 7.55/7.80               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 7.55/7.80  thf('96', plain,
% 7.55/7.80      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.55/7.80         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 7.55/7.80          | ~ (m1_connsp_2 @ X34 @ X35 @ X36)
% 7.55/7.80          | (r2_hidden @ X36 @ X34)
% 7.55/7.80          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 7.55/7.80          | ~ (l1_pre_topc @ X35)
% 7.55/7.80          | ~ (v2_pre_topc @ X35)
% 7.55/7.80          | (v2_struct_0 @ X35))),
% 7.55/7.80      inference('cnf', [status(esa)], [t6_connsp_2])).
% 7.55/7.80  thf('97', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((v2_struct_0 @ sk_A)
% 7.55/7.80          | ~ (v2_pre_topc @ sk_A)
% 7.55/7.80          | ~ (l1_pre_topc @ sk_A)
% 7.55/7.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | (r2_hidden @ X0 @ sk_B)
% 7.55/7.80          | ~ (m1_connsp_2 @ sk_B @ sk_A @ X0))),
% 7.55/7.80      inference('sup-', [status(thm)], ['95', '96'])).
% 7.55/7.80  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.80  thf('100', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((v2_struct_0 @ sk_A)
% 7.55/7.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.80          | (r2_hidden @ X0 @ sk_B)
% 7.55/7.80          | ~ (m1_connsp_2 @ sk_B @ sk_A @ X0))),
% 7.55/7.80      inference('demod', [status(thm)], ['97', '98', '99'])).
% 7.55/7.80  thf('101', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | ~ (m1_connsp_2 @ sk_B @ sk_A @ 
% 7.55/7.80               (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.80          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 7.55/7.80          | (v2_struct_0 @ sk_A))),
% 7.55/7.80      inference('sup-', [status(thm)], ['94', '100'])).
% 7.55/7.80  thf('102', plain,
% 7.55/7.80      (![X0 : $i]:
% 7.55/7.80         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.80          | (v2_struct_0 @ sk_A)
% 7.55/7.80          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 7.55/7.80          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.55/7.81      inference('sup-', [status(thm)], ['93', '101'])).
% 7.55/7.81  thf('103', plain,
% 7.55/7.81      (![X0 : $i]:
% 7.55/7.81         ((r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 7.55/7.81          | (v2_struct_0 @ sk_A)
% 7.55/7.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.55/7.81      inference('simplify', [status(thm)], ['102'])).
% 7.55/7.81  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('105', plain,
% 7.55/7.81      (![X0 : $i]:
% 7.55/7.81         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 7.55/7.81          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B))),
% 7.55/7.81      inference('clc', [status(thm)], ['103', '104'])).
% 7.55/7.81  thf('106', plain,
% 7.55/7.81      (![X1 : $i, X3 : $i]:
% 7.55/7.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.55/7.81      inference('cnf', [status(esa)], [d3_tarski])).
% 7.55/7.81  thf('107', plain,
% 7.55/7.81      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 7.55/7.81        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 7.55/7.81      inference('sup-', [status(thm)], ['105', '106'])).
% 7.55/7.81  thf('108', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.55/7.81      inference('simplify', [status(thm)], ['107'])).
% 7.55/7.81  thf('109', plain,
% 7.55/7.81      (![X4 : $i, X6 : $i]:
% 7.55/7.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 7.55/7.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.55/7.81  thf('110', plain,
% 7.55/7.81      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.81        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['108', '109'])).
% 7.55/7.81  thf('111', plain,
% 7.55/7.81      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['72', '110'])).
% 7.55/7.81  thf('112', plain,
% 7.55/7.81      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.55/7.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.81      inference('demod', [status(thm)], ['76', '77'])).
% 7.55/7.81  thf(t55_tops_1, axiom,
% 7.55/7.81    (![A:$i]:
% 7.55/7.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.55/7.81       ( ![B:$i]:
% 7.55/7.81         ( ( l1_pre_topc @ B ) =>
% 7.55/7.81           ( ![C:$i]:
% 7.55/7.81             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.81               ( ![D:$i]:
% 7.55/7.81                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 7.55/7.81                   ( ( ( v3_pre_topc @ D @ B ) =>
% 7.55/7.81                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 7.55/7.81                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 7.55/7.81                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 7.55/7.81  thf('113', plain,
% 7.55/7.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 7.55/7.81         (~ (l1_pre_topc @ X21)
% 7.55/7.81          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.55/7.81          | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81          | (v3_pre_topc @ X23 @ X24)
% 7.55/7.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81          | ~ (l1_pre_topc @ X24)
% 7.55/7.81          | ~ (v2_pre_topc @ X24))),
% 7.55/7.81      inference('cnf', [status(esa)], [t55_tops_1])).
% 7.55/7.81  thf('114', plain,
% 7.55/7.81      ((![X23 : $i, X24 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81           | ~ (l1_pre_topc @ X24)
% 7.55/7.81           | ~ (v2_pre_topc @ X24)
% 7.55/7.81           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81           | (v3_pre_topc @ X23 @ X24)))
% 7.55/7.81         <= ((![X23 : $i, X24 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81                 | ~ (l1_pre_topc @ X24)
% 7.55/7.81                 | ~ (v2_pre_topc @ X24)
% 7.55/7.81                 | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81                 | (v3_pre_topc @ X23 @ X24))))),
% 7.55/7.81      inference('split', [status(esa)], ['113'])).
% 7.55/7.81  thf('115', plain,
% 7.55/7.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('116', plain,
% 7.55/7.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 7.55/7.81         (~ (l1_pre_topc @ X21)
% 7.55/7.81          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.55/7.81          | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81          | (v3_pre_topc @ X23 @ X24)
% 7.55/7.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81          | ~ (l1_pre_topc @ X24)
% 7.55/7.81          | ~ (v2_pre_topc @ X24))),
% 7.55/7.81      inference('cnf', [status(esa)], [t55_tops_1])).
% 7.55/7.81  thf('117', plain,
% 7.55/7.81      ((![X21 : $i, X22 : $i]:
% 7.55/7.81          (~ (l1_pre_topc @ X21)
% 7.55/7.81           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))
% 7.55/7.81         <= ((![X21 : $i, X22 : $i]:
% 7.55/7.81                (~ (l1_pre_topc @ X21)
% 7.55/7.81                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))))),
% 7.55/7.81      inference('split', [status(esa)], ['116'])).
% 7.55/7.81  thf('118', plain,
% 7.55/7.81      ((~ (l1_pre_topc @ sk_A))
% 7.55/7.81         <= ((![X21 : $i, X22 : $i]:
% 7.55/7.81                (~ (l1_pre_topc @ X21)
% 7.55/7.81                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['115', '117'])).
% 7.55/7.81  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('120', plain,
% 7.55/7.81      (~
% 7.55/7.81       (![X21 : $i, X22 : $i]:
% 7.55/7.81          (~ (l1_pre_topc @ X21)
% 7.55/7.81           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))),
% 7.55/7.81      inference('demod', [status(thm)], ['118', '119'])).
% 7.55/7.81  thf('121', plain,
% 7.55/7.81      ((![X23 : $i, X24 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81           | ~ (l1_pre_topc @ X24)
% 7.55/7.81           | ~ (v2_pre_topc @ X24)
% 7.55/7.81           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81           | (v3_pre_topc @ X23 @ X24))) | 
% 7.55/7.81       (![X21 : $i, X22 : $i]:
% 7.55/7.81          (~ (l1_pre_topc @ X21)
% 7.55/7.81           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))))),
% 7.55/7.81      inference('split', [status(esa)], ['116'])).
% 7.55/7.81  thf('122', plain,
% 7.55/7.81      ((![X23 : $i, X24 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81           | ~ (l1_pre_topc @ X24)
% 7.55/7.81           | ~ (v2_pre_topc @ X24)
% 7.55/7.81           | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81           | (v3_pre_topc @ X23 @ X24)))),
% 7.55/7.81      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 7.55/7.81  thf('123', plain,
% 7.55/7.81      (![X23 : $i, X24 : $i]:
% 7.55/7.81         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.55/7.81          | ~ (l1_pre_topc @ X24)
% 7.55/7.81          | ~ (v2_pre_topc @ X24)
% 7.55/7.81          | ((k1_tops_1 @ X24 @ X23) != (X23))
% 7.55/7.81          | (v3_pre_topc @ X23 @ X24))),
% 7.55/7.81      inference('simpl_trail', [status(thm)], ['114', '122'])).
% 7.55/7.81  thf('124', plain,
% 7.55/7.81      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 7.55/7.81        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.81            != (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.81        | ~ (v2_pre_topc @ sk_A)
% 7.55/7.81        | ~ (l1_pre_topc @ sk_A))),
% 7.55/7.81      inference('sup-', [status(thm)], ['112', '123'])).
% 7.55/7.81  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('127', plain,
% 7.55/7.81      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 7.55/7.81        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.81            != (k1_tops_1 @ sk_A @ sk_B)))),
% 7.55/7.81      inference('demod', [status(thm)], ['124', '125', '126'])).
% 7.55/7.81  thf('128', plain,
% 7.55/7.81      (((((k1_tops_1 @ sk_A @ sk_B) != (k1_tops_1 @ sk_A @ sk_B))
% 7.55/7.81         | (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['111', '127'])).
% 7.55/7.81  thf('129', plain,
% 7.55/7.81      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['72', '110'])).
% 7.55/7.81  thf('130', plain,
% 7.55/7.81      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['72', '110'])).
% 7.55/7.81  thf('131', plain,
% 7.55/7.81      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['72', '110'])).
% 7.55/7.81  thf('132', plain,
% 7.55/7.81      (((((sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A)))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 7.55/7.81  thf('133', plain,
% 7.55/7.81      (((v3_pre_topc @ sk_B @ sk_A))
% 7.55/7.81         <= ((![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (r1_tarski @ (sk_D @ X37) @ sk_B))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) & 
% 7.55/7.81             (![X37 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81                 | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81                 | (m1_subset_1 @ (sk_D @ X37) @ 
% 7.55/7.81                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 7.55/7.81      inference('simplify', [status(thm)], ['132'])).
% 7.55/7.81  thf('134', plain,
% 7.55/7.81      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 7.55/7.81      inference('split', [status(esa)], ['0'])).
% 7.55/7.81  thf('135', plain,
% 7.55/7.81      (~
% 7.55/7.81       (![X37 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81           | (m1_connsp_2 @ (sk_D @ X37) @ sk_A @ X37))) | 
% 7.55/7.81       ~
% 7.55/7.81       (![X37 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81           | (m1_subset_1 @ (sk_D @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 7.55/7.81       ~
% 7.55/7.81       (![X37 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 7.55/7.81           | ~ (r2_hidden @ X37 @ sk_B)
% 7.55/7.81           | (r1_tarski @ (sk_D @ X37) @ sk_B))) | 
% 7.55/7.81       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.81      inference('sup-', [status(thm)], ['133', '134'])).
% 7.55/7.81  thf('136', plain,
% 7.55/7.81      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('137', plain,
% 7.55/7.81      (((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.81      inference('split', [status(esa)], ['136'])).
% 7.55/7.81  thf('138', plain,
% 7.55/7.81      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('split', [status(esa)], ['136'])).
% 7.55/7.81  thf('139', plain,
% 7.55/7.81      (![X0 : $i]:
% 7.55/7.81         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 7.55/7.81      inference('sup-', [status(thm)], ['11', '12'])).
% 7.55/7.81  thf('140', plain,
% 7.55/7.81      (((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['138', '139'])).
% 7.55/7.81  thf('141', plain,
% 7.55/7.81      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 7.55/7.81      inference('sup-', [status(thm)], ['18', '19'])).
% 7.55/7.81  thf('142', plain,
% 7.55/7.81      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['140', '141'])).
% 7.55/7.81  thf('143', plain,
% 7.55/7.81      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.55/7.81      inference('split', [status(esa)], ['2'])).
% 7.55/7.81  thf('144', plain,
% 7.55/7.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf(t5_connsp_2, axiom,
% 7.55/7.81    (![A:$i]:
% 7.55/7.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.55/7.81       ( ![B:$i]:
% 7.55/7.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.55/7.81           ( ![C:$i]:
% 7.55/7.81             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 7.55/7.81               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 7.55/7.81                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 7.55/7.81  thf('145', plain,
% 7.55/7.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.55/7.81         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 7.55/7.81          | ~ (v3_pre_topc @ X31 @ X32)
% 7.55/7.81          | ~ (r2_hidden @ X33 @ X31)
% 7.55/7.81          | (m1_connsp_2 @ X31 @ X32 @ X33)
% 7.55/7.81          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 7.55/7.81          | ~ (l1_pre_topc @ X32)
% 7.55/7.81          | ~ (v2_pre_topc @ X32)
% 7.55/7.81          | (v2_struct_0 @ X32))),
% 7.55/7.81      inference('cnf', [status(esa)], [t5_connsp_2])).
% 7.55/7.81  thf('146', plain,
% 7.55/7.81      (![X0 : $i]:
% 7.55/7.81         ((v2_struct_0 @ sk_A)
% 7.55/7.81          | ~ (v2_pre_topc @ sk_A)
% 7.55/7.81          | ~ (l1_pre_topc @ sk_A)
% 7.55/7.81          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.81          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 7.55/7.81          | ~ (r2_hidden @ X0 @ sk_B)
% 7.55/7.81          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.81      inference('sup-', [status(thm)], ['144', '145'])).
% 7.55/7.81  thf('147', plain, ((v2_pre_topc @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('149', plain,
% 7.55/7.81      (![X0 : $i]:
% 7.55/7.81         ((v2_struct_0 @ sk_A)
% 7.55/7.81          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.81          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 7.55/7.81          | ~ (r2_hidden @ X0 @ sk_B)
% 7.55/7.81          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.55/7.81      inference('demod', [status(thm)], ['146', '147', '148'])).
% 7.55/7.81  thf('150', plain,
% 7.55/7.81      ((![X0 : $i]:
% 7.55/7.81          (~ (r2_hidden @ X0 @ sk_B)
% 7.55/7.81           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 7.55/7.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 7.55/7.81           | (v2_struct_0 @ sk_A)))
% 7.55/7.81         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['143', '149'])).
% 7.55/7.81  thf('151', plain,
% 7.55/7.81      ((((v2_struct_0 @ sk_A)
% 7.55/7.81         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 7.55/7.81         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 7.55/7.81         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['142', '150'])).
% 7.55/7.81  thf('152', plain,
% 7.55/7.81      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('split', [status(esa)], ['136'])).
% 7.55/7.81  thf('153', plain,
% 7.55/7.81      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 7.55/7.81         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('demod', [status(thm)], ['151', '152'])).
% 7.55/7.81  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('155', plain,
% 7.55/7.81      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 7.55/7.81         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 7.55/7.81      inference('clc', [status(thm)], ['153', '154'])).
% 7.55/7.81  thf('156', plain,
% 7.55/7.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.55/7.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.55/7.81  thf('157', plain,
% 7.55/7.81      ((![X38 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.81           | ~ (r1_tarski @ X38 @ sk_B)))
% 7.55/7.81         <= ((![X38 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.81                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 7.55/7.81      inference('split', [status(esa)], ['0'])).
% 7.55/7.81  thf('158', plain,
% 7.55/7.81      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 7.55/7.81         <= ((![X38 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.81                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 7.55/7.81      inference('sup-', [status(thm)], ['156', '157'])).
% 7.55/7.81  thf('159', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 7.55/7.81      inference('simplify', [status(thm)], ['15'])).
% 7.55/7.81  thf('160', plain,
% 7.55/7.81      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 7.55/7.81         <= ((![X38 : $i]:
% 7.55/7.81                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.81                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 7.55/7.81      inference('demod', [status(thm)], ['158', '159'])).
% 7.55/7.81  thf('161', plain,
% 7.55/7.81      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 7.55/7.81       ~
% 7.55/7.81       (![X38 : $i]:
% 7.55/7.81          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.55/7.81           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 7.55/7.81           | ~ (r1_tarski @ X38 @ sk_B)))),
% 7.55/7.81      inference('sup-', [status(thm)], ['155', '160'])).
% 7.55/7.81  thf('162', plain, ($false),
% 7.55/7.81      inference('sat_resolution*', [status(thm)],
% 7.55/7.81                ['1', '3', '5', '7', '135', '137', '161'])).
% 7.55/7.81  
% 7.55/7.81  % SZS output end Refutation
% 7.55/7.81  
% 7.67/7.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
