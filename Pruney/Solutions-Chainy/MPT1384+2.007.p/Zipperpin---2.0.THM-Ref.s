%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6wNf72VSm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:57 EST 2020

% Result     : Theorem 36.85s
% Output     : Refutation 36.85s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 269 expanded)
%              Number of leaves         :   26 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          : 1998 (4778 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X30 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
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
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X29: $i] :
        ( ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_connsp_2 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,
    ( ! [X29: $i] :
        ( ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('48',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
        | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ sk_B ) ) ) ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('78',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf('83',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D @ X29 ) @ sk_A @ X29 ) )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( m1_subset_1 @ ( sk_D @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X29 @ sk_B )
          | ( r1_tarski @ ( sk_D @ X29 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['85'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('89',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( m1_connsp_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['85'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X30 @ sk_B ) )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('110',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','84','86','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6wNf72VSm
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 36.85/37.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 36.85/37.08  % Solved by: fo/fo7.sh
% 36.85/37.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.85/37.08  % done 16825 iterations in 36.594s
% 36.85/37.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 36.85/37.08  % SZS output start Refutation
% 36.85/37.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 36.85/37.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 36.85/37.08  thf(sk_B_type, type, sk_B: $i).
% 36.85/37.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.85/37.08  thf(sk_D_type, type, sk_D: $i > $i).
% 36.85/37.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 36.85/37.08  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 36.85/37.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 36.85/37.08  thf(sk_A_type, type, sk_A: $i).
% 36.85/37.08  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 36.85/37.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 36.85/37.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 36.85/37.08  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 36.85/37.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 36.85/37.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 36.85/37.08  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 36.85/37.08  thf(t9_connsp_2, conjecture,
% 36.85/37.08    (![A:$i]:
% 36.85/37.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.85/37.08       ( ![B:$i]:
% 36.85/37.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08           ( ( v3_pre_topc @ B @ A ) <=>
% 36.85/37.08             ( ![C:$i]:
% 36.85/37.08               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.85/37.08                 ( ~( ( r2_hidden @ C @ B ) & 
% 36.85/37.08                      ( ![D:$i]:
% 36.85/37.08                        ( ( m1_subset_1 @
% 36.85/37.08                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 36.85/37.08                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 36.85/37.08  thf(zf_stmt_0, negated_conjecture,
% 36.85/37.08    (~( ![A:$i]:
% 36.85/37.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 36.85/37.08            ( l1_pre_topc @ A ) ) =>
% 36.85/37.08          ( ![B:$i]:
% 36.85/37.08            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08              ( ( v3_pre_topc @ B @ A ) <=>
% 36.85/37.08                ( ![C:$i]:
% 36.85/37.08                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.85/37.08                    ( ~( ( r2_hidden @ C @ B ) & 
% 36.85/37.08                         ( ![D:$i]:
% 36.85/37.08                           ( ( m1_subset_1 @
% 36.85/37.08                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 36.85/37.08                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 36.85/37.08    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 36.85/37.08  thf('0', plain,
% 36.85/37.08      (![X30 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08          | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.08          | ~ (r1_tarski @ X30 @ sk_B)
% 36.85/37.08          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('1', plain,
% 36.85/37.08      ((![X30 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.08           | ~ (r1_tarski @ X30 @ sk_B))) | 
% 36.85/37.08       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('split', [status(esa)], ['0'])).
% 36.85/37.08  thf('2', plain,
% 36.85/37.08      (![X29 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08          | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08          | (r1_tarski @ (sk_D @ X29) @ sk_B)
% 36.85/37.08          | (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('3', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (r1_tarski @ (sk_D @ X29) @ sk_B))) | 
% 36.85/37.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('split', [status(esa)], ['2'])).
% 36.85/37.08  thf('4', plain,
% 36.85/37.08      (![X29 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08          | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08          | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29)
% 36.85/37.08          | (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('5', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) | 
% 36.85/37.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('split', [status(esa)], ['4'])).
% 36.85/37.08  thf('6', plain,
% 36.85/37.08      (![X29 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08          | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08          | (m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08          | (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('7', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 36.85/37.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('split', [status(esa)], ['6'])).
% 36.85/37.08  thf(d3_tarski, axiom,
% 36.85/37.08    (![A:$i,B:$i]:
% 36.85/37.08     ( ( r1_tarski @ A @ B ) <=>
% 36.85/37.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 36.85/37.08  thf('8', plain,
% 36.85/37.08      (![X1 : $i, X3 : $i]:
% 36.85/37.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('9', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf(t3_subset, axiom,
% 36.85/37.08    (![A:$i,B:$i]:
% 36.85/37.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 36.85/37.08  thf('10', plain,
% 36.85/37.08      (![X7 : $i, X8 : $i]:
% 36.85/37.08         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 36.85/37.08      inference('cnf', [status(esa)], [t3_subset])).
% 36.85/37.08  thf('11', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 36.85/37.08      inference('sup-', [status(thm)], ['9', '10'])).
% 36.85/37.08  thf('12', plain,
% 36.85/37.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.85/37.08         (~ (r2_hidden @ X0 @ X1)
% 36.85/37.08          | (r2_hidden @ X0 @ X2)
% 36.85/37.08          | ~ (r1_tarski @ X1 @ X2))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('13', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 36.85/37.08      inference('sup-', [status(thm)], ['11', '12'])).
% 36.85/37.08  thf('14', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((r1_tarski @ sk_B @ X0)
% 36.85/37.08          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['8', '13'])).
% 36.85/37.08  thf(d10_xboole_0, axiom,
% 36.85/37.08    (![A:$i,B:$i]:
% 36.85/37.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 36.85/37.08  thf('15', plain,
% 36.85/37.08      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 36.85/37.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.85/37.08  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 36.85/37.08      inference('simplify', [status(thm)], ['15'])).
% 36.85/37.08  thf('17', plain,
% 36.85/37.08      (![X7 : $i, X9 : $i]:
% 36.85/37.08         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 36.85/37.08      inference('cnf', [status(esa)], [t3_subset])).
% 36.85/37.08  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 36.85/37.08      inference('sup-', [status(thm)], ['16', '17'])).
% 36.85/37.08  thf(t4_subset, axiom,
% 36.85/37.08    (![A:$i,B:$i,C:$i]:
% 36.85/37.08     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 36.85/37.08       ( m1_subset_1 @ A @ C ) ))).
% 36.85/37.08  thf('19', plain,
% 36.85/37.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 36.85/37.08         (~ (r2_hidden @ X10 @ X11)
% 36.85/37.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 36.85/37.08          | (m1_subset_1 @ X10 @ X12))),
% 36.85/37.08      inference('cnf', [status(esa)], [t4_subset])).
% 36.85/37.08  thf('20', plain,
% 36.85/37.08      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 36.85/37.08      inference('sup-', [status(thm)], ['18', '19'])).
% 36.85/37.08  thf('21', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((r1_tarski @ sk_B @ X0)
% 36.85/37.08          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['14', '20'])).
% 36.85/37.08  thf('22', plain,
% 36.85/37.08      (![X1 : $i, X3 : $i]:
% 36.85/37.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('23', plain,
% 36.85/37.08      (![X29 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08          | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08          | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29)
% 36.85/37.08          | (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('24', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))))),
% 36.85/37.08      inference('split', [status(esa)], ['23'])).
% 36.85/37.08  thf('25', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('26', plain,
% 36.85/37.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 36.85/37.08         (~ (r2_hidden @ X10 @ X11)
% 36.85/37.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 36.85/37.08          | (m1_subset_1 @ X10 @ X12))),
% 36.85/37.08      inference('cnf', [status(esa)], [t4_subset])).
% 36.85/37.08  thf('27', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 36.85/37.08      inference('sup-', [status(thm)], ['25', '26'])).
% 36.85/37.08  thf('28', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          ((m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29)
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))))),
% 36.85/37.08      inference('clc', [status(thm)], ['24', '27'])).
% 36.85/37.08  thf('29', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 36.85/37.08              (sk_C @ X0 @ sk_B))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['22', '28'])).
% 36.85/37.08  thf('30', plain,
% 36.85/37.08      (![X1 : $i, X3 : $i]:
% 36.85/37.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('31', plain,
% 36.85/37.08      (![X29 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08          | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08          | (m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08          | (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('32', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('split', [status(esa)], ['31'])).
% 36.85/37.08  thf('33', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 36.85/37.08      inference('sup-', [status(thm)], ['25', '26'])).
% 36.85/37.08  thf('34', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          ((m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('clc', [status(thm)], ['32', '33'])).
% 36.85/37.08  thf('35', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 36.85/37.08              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['30', '34'])).
% 36.85/37.08  thf(d1_connsp_2, axiom,
% 36.85/37.08    (![A:$i]:
% 36.85/37.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.85/37.08       ( ![B:$i]:
% 36.85/37.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 36.85/37.08           ( ![C:$i]:
% 36.85/37.08             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 36.85/37.08                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 36.85/37.08  thf('36', plain,
% 36.85/37.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 36.85/37.08          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 36.85/37.08          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 36.85/37.08          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 36.85/37.08          | ~ (l1_pre_topc @ X21)
% 36.85/37.08          | ~ (v2_pre_topc @ X21)
% 36.85/37.08          | (v2_struct_0 @ X21))),
% 36.85/37.08      inference('cnf', [status(esa)], [d1_connsp_2])).
% 36.85/37.08  thf('37', plain,
% 36.85/37.08      ((![X0 : $i, X1 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (v2_struct_0 @ sk_A)
% 36.85/37.08           | ~ (v2_pre_topc @ sk_A)
% 36.85/37.08           | ~ (l1_pre_topc @ sk_A)
% 36.85/37.08           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 36.85/37.08           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['35', '36'])).
% 36.85/37.08  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('40', plain,
% 36.85/37.08      ((![X0 : $i, X1 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (v2_struct_0 @ sk_A)
% 36.85/37.08           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | ~ (m1_connsp_2 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 36.85/37.08           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('demod', [status(thm)], ['37', '38', '39'])).
% 36.85/37.08  thf('41', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | (v2_struct_0 @ sk_A)
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['29', '40'])).
% 36.85/37.08  thf('42', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((v2_struct_0 @ sk_A)
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('simplify', [status(thm)], ['41'])).
% 36.85/37.08  thf('43', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | (v2_struct_0 @ sk_A)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['21', '42'])).
% 36.85/37.08  thf('44', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((v2_struct_0 @ sk_A)
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('simplify', [status(thm)], ['43'])).
% 36.85/37.08  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('46', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('clc', [status(thm)], ['44', '45'])).
% 36.85/37.08  thf('47', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((r1_tarski @ sk_B @ X0)
% 36.85/37.08          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['14', '20'])).
% 36.85/37.08  thf('48', plain,
% 36.85/37.08      ((![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (r1_tarski @ (sk_D @ X29) @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))))),
% 36.85/37.08      inference('split', [status(esa)], ['2'])).
% 36.85/37.08  thf('49', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 36.85/37.08           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['47', '48'])).
% 36.85/37.08  thf('50', plain,
% 36.85/37.08      (![X1 : $i, X3 : $i]:
% 36.85/37.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('51', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))))),
% 36.85/37.08      inference('clc', [status(thm)], ['49', '50'])).
% 36.85/37.08  thf('52', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('53', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (m1_subset_1 @ (sk_D @ (sk_C @ X0 @ sk_B)) @ 
% 36.85/37.08              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['30', '34'])).
% 36.85/37.08  thf(t48_tops_1, axiom,
% 36.85/37.08    (![A:$i]:
% 36.85/37.08     ( ( l1_pre_topc @ A ) =>
% 36.85/37.08       ( ![B:$i]:
% 36.85/37.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08           ( ![C:$i]:
% 36.85/37.08             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08               ( ( r1_tarski @ B @ C ) =>
% 36.85/37.08                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 36.85/37.08  thf('54', plain,
% 36.85/37.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 36.85/37.08          | ~ (r1_tarski @ X17 @ X19)
% 36.85/37.08          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 36.85/37.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 36.85/37.08          | ~ (l1_pre_topc @ X18))),
% 36.85/37.08      inference('cnf', [status(esa)], [t48_tops_1])).
% 36.85/37.08  thf('55', plain,
% 36.85/37.08      ((![X0 : $i, X1 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | ~ (l1_pre_topc @ sk_A)
% 36.85/37.08           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ X1))
% 36.85/37.08           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['53', '54'])).
% 36.85/37.08  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('57', plain,
% 36.85/37.08      ((![X0 : $i, X1 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ X1))
% 36.85/37.08           | ~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ X1)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('demod', [status(thm)], ['55', '56'])).
% 36.85/37.08  thf('58', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          (~ (r1_tarski @ (sk_D @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 36.85/37.08           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['52', '57'])).
% 36.85/37.08  thf('59', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 36.85/37.08              (k1_tops_1 @ sk_A @ sk_B))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['51', '58'])).
% 36.85/37.08  thf('60', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))) @ 
% 36.85/37.08            (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('simplify', [status(thm)], ['59'])).
% 36.85/37.08  thf('61', plain,
% 36.85/37.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.85/37.08         (~ (r2_hidden @ X0 @ X1)
% 36.85/37.08          | (r2_hidden @ X0 @ X2)
% 36.85/37.08          | ~ (r1_tarski @ X1 @ X2))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('62', plain,
% 36.85/37.08      ((![X0 : $i, X1 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08           | ~ (r2_hidden @ X1 @ 
% 36.85/37.08                (k1_tops_1 @ sk_A @ (sk_D @ (sk_C @ X0 @ sk_B))))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['60', '61'])).
% 36.85/37.08  thf('63', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r1_tarski @ sk_B @ X0)
% 36.85/37.08           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['46', '62'])).
% 36.85/37.08  thf('64', plain,
% 36.85/37.08      ((![X0 : $i]:
% 36.85/37.08          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08           | (r1_tarski @ sk_B @ X0)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('simplify', [status(thm)], ['63'])).
% 36.85/37.08  thf('65', plain,
% 36.85/37.08      (![X1 : $i, X3 : $i]:
% 36.85/37.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 36.85/37.08      inference('cnf', [status(esa)], [d3_tarski])).
% 36.85/37.08  thf('66', plain,
% 36.85/37.08      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['64', '65'])).
% 36.85/37.08  thf('67', plain,
% 36.85/37.08      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('simplify', [status(thm)], ['66'])).
% 36.85/37.08  thf('68', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf(t44_tops_1, axiom,
% 36.85/37.08    (![A:$i]:
% 36.85/37.08     ( ( l1_pre_topc @ A ) =>
% 36.85/37.08       ( ![B:$i]:
% 36.85/37.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 36.85/37.08  thf('69', plain,
% 36.85/37.08      (![X15 : $i, X16 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 36.85/37.08          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 36.85/37.08          | ~ (l1_pre_topc @ X16))),
% 36.85/37.08      inference('cnf', [status(esa)], [t44_tops_1])).
% 36.85/37.08  thf('70', plain,
% 36.85/37.08      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 36.85/37.08      inference('sup-', [status(thm)], ['68', '69'])).
% 36.85/37.08  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('72', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 36.85/37.08      inference('demod', [status(thm)], ['70', '71'])).
% 36.85/37.08  thf('73', plain,
% 36.85/37.08      (![X4 : $i, X6 : $i]:
% 36.85/37.08         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 36.85/37.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 36.85/37.08  thf('74', plain,
% 36.85/37.08      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 36.85/37.08        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['72', '73'])).
% 36.85/37.08  thf('75', plain,
% 36.85/37.08      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup-', [status(thm)], ['67', '74'])).
% 36.85/37.08  thf('76', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf(fc9_tops_1, axiom,
% 36.85/37.08    (![A:$i,B:$i]:
% 36.85/37.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 36.85/37.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 36.85/37.08       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 36.85/37.08  thf('77', plain,
% 36.85/37.08      (![X13 : $i, X14 : $i]:
% 36.85/37.08         (~ (l1_pre_topc @ X13)
% 36.85/37.08          | ~ (v2_pre_topc @ X13)
% 36.85/37.08          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 36.85/37.08          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 36.85/37.08      inference('cnf', [status(esa)], [fc9_tops_1])).
% 36.85/37.08  thf('78', plain,
% 36.85/37.08      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 36.85/37.08        | ~ (v2_pre_topc @ sk_A)
% 36.85/37.08        | ~ (l1_pre_topc @ sk_A))),
% 36.85/37.08      inference('sup-', [status(thm)], ['76', '77'])).
% 36.85/37.08  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('81', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 36.85/37.08      inference('demod', [status(thm)], ['78', '79', '80'])).
% 36.85/37.08  thf('82', plain,
% 36.85/37.08      (((v3_pre_topc @ sk_B @ sk_A))
% 36.85/37.08         <= ((![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (r1_tarski @ (sk_D @ X29) @ sk_B))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) & 
% 36.85/37.08             (![X29 : $i]:
% 36.85/37.08                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08                 | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08                 | (m1_subset_1 @ (sk_D @ X29) @ 
% 36.85/37.08                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 36.85/37.08      inference('sup+', [status(thm)], ['75', '81'])).
% 36.85/37.08  thf('83', plain,
% 36.85/37.08      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 36.85/37.08      inference('split', [status(esa)], ['0'])).
% 36.85/37.08  thf('84', plain,
% 36.85/37.08      (~
% 36.85/37.08       (![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_connsp_2 @ (sk_D @ X29) @ sk_A @ X29))) | 
% 36.85/37.08       ~
% 36.85/37.08       (![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (m1_subset_1 @ (sk_D @ X29) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 36.85/37.08       ~
% 36.85/37.08       (![X29 : $i]:
% 36.85/37.08          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 36.85/37.08           | ~ (r2_hidden @ X29 @ sk_B)
% 36.85/37.08           | (r1_tarski @ (sk_D @ X29) @ sk_B))) | 
% 36.85/37.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('sup-', [status(thm)], ['82', '83'])).
% 36.85/37.08  thf('85', plain,
% 36.85/37.08      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf('86', plain,
% 36.85/37.08      (((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.08      inference('split', [status(esa)], ['85'])).
% 36.85/37.08  thf('87', plain,
% 36.85/37.08      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.08      inference('split', [status(esa)], ['85'])).
% 36.85/37.08  thf('88', plain,
% 36.85/37.08      (![X0 : $i]:
% 36.85/37.08         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 36.85/37.08      inference('sup-', [status(thm)], ['11', '12'])).
% 36.85/37.08  thf('89', plain,
% 36.85/37.08      (((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['87', '88'])).
% 36.85/37.08  thf('90', plain,
% 36.85/37.08      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 36.85/37.08      inference('sup-', [status(thm)], ['18', '19'])).
% 36.85/37.08  thf('91', plain,
% 36.85/37.08      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.08         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.08      inference('sup-', [status(thm)], ['89', '90'])).
% 36.85/37.08  thf('92', plain,
% 36.85/37.08      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 36.85/37.08      inference('split', [status(esa)], ['2'])).
% 36.85/37.08  thf('93', plain,
% 36.85/37.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.08  thf(t5_connsp_2, axiom,
% 36.85/37.08    (![A:$i]:
% 36.85/37.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 36.85/37.08       ( ![B:$i]:
% 36.85/37.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 36.85/37.08           ( ![C:$i]:
% 36.85/37.08             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 36.85/37.08               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 36.85/37.08                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 36.85/37.08  thf('94', plain,
% 36.85/37.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 36.85/37.08         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 36.85/37.08          | ~ (v3_pre_topc @ X26 @ X27)
% 36.85/37.08          | ~ (r2_hidden @ X28 @ X26)
% 36.85/37.09          | (m1_connsp_2 @ X26 @ X27 @ X28)
% 36.85/37.09          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 36.85/37.09          | ~ (l1_pre_topc @ X27)
% 36.85/37.09          | ~ (v2_pre_topc @ X27)
% 36.85/37.09          | (v2_struct_0 @ X27))),
% 36.85/37.09      inference('cnf', [status(esa)], [t5_connsp_2])).
% 36.85/37.09  thf('95', plain,
% 36.85/37.09      (![X0 : $i]:
% 36.85/37.09         ((v2_struct_0 @ sk_A)
% 36.85/37.09          | ~ (v2_pre_topc @ sk_A)
% 36.85/37.09          | ~ (l1_pre_topc @ sk_A)
% 36.85/37.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.85/37.09          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 36.85/37.09          | ~ (r2_hidden @ X0 @ sk_B)
% 36.85/37.09          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.09      inference('sup-', [status(thm)], ['93', '94'])).
% 36.85/37.09  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 36.85/37.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.09  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 36.85/37.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.09  thf('98', plain,
% 36.85/37.09      (![X0 : $i]:
% 36.85/37.09         ((v2_struct_0 @ sk_A)
% 36.85/37.09          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.85/37.09          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 36.85/37.09          | ~ (r2_hidden @ X0 @ sk_B)
% 36.85/37.09          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 36.85/37.09      inference('demod', [status(thm)], ['95', '96', '97'])).
% 36.85/37.09  thf('99', plain,
% 36.85/37.09      ((![X0 : $i]:
% 36.85/37.09          (~ (r2_hidden @ X0 @ sk_B)
% 36.85/37.09           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 36.85/37.09           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 36.85/37.09           | (v2_struct_0 @ sk_A)))
% 36.85/37.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 36.85/37.09      inference('sup-', [status(thm)], ['92', '98'])).
% 36.85/37.09  thf('100', plain,
% 36.85/37.09      ((((v2_struct_0 @ sk_A)
% 36.85/37.09         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 36.85/37.09         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 36.85/37.09         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.09      inference('sup-', [status(thm)], ['91', '99'])).
% 36.85/37.09  thf('101', plain,
% 36.85/37.09      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.09      inference('split', [status(esa)], ['85'])).
% 36.85/37.09  thf('102', plain,
% 36.85/37.09      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 36.85/37.09         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.09      inference('demod', [status(thm)], ['100', '101'])).
% 36.85/37.09  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 36.85/37.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.09  thf('104', plain,
% 36.85/37.09      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 36.85/37.09         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.09      inference('clc', [status(thm)], ['102', '103'])).
% 36.85/37.09  thf('105', plain,
% 36.85/37.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 36.85/37.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.85/37.09  thf('106', plain,
% 36.85/37.09      ((![X30 : $i]:
% 36.85/37.09          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.09           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.09           | ~ (r1_tarski @ X30 @ sk_B)))
% 36.85/37.09         <= ((![X30 : $i]:
% 36.85/37.09                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.09                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.09                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 36.85/37.09      inference('split', [status(esa)], ['0'])).
% 36.85/37.09  thf('107', plain,
% 36.85/37.09      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 36.85/37.09         <= ((![X30 : $i]:
% 36.85/37.09                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.09                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.09                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 36.85/37.09      inference('sup-', [status(thm)], ['105', '106'])).
% 36.85/37.09  thf('108', plain,
% 36.85/37.09      ((~ (r1_tarski @ sk_B @ sk_B))
% 36.85/37.09         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 36.85/37.09             (![X30 : $i]:
% 36.85/37.09                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.09                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.09                 | ~ (r1_tarski @ X30 @ sk_B))) & 
% 36.85/37.09             ((r2_hidden @ sk_C_1 @ sk_B)))),
% 36.85/37.09      inference('sup-', [status(thm)], ['104', '107'])).
% 36.85/37.09  thf('109', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 36.85/37.09      inference('simplify', [status(thm)], ['15'])).
% 36.85/37.09  thf('110', plain,
% 36.85/37.09      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 36.85/37.09       ~
% 36.85/37.09       (![X30 : $i]:
% 36.85/37.09          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 36.85/37.09           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 36.85/37.09           | ~ (r1_tarski @ X30 @ sk_B)))),
% 36.85/37.09      inference('demod', [status(thm)], ['108', '109'])).
% 36.85/37.09  thf('111', plain, ($false),
% 36.85/37.09      inference('sat_resolution*', [status(thm)],
% 36.85/37.09                ['1', '3', '5', '7', '84', '86', '110'])).
% 36.85/37.09  
% 36.85/37.09  % SZS output end Refutation
% 36.85/37.09  
% 36.85/37.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
