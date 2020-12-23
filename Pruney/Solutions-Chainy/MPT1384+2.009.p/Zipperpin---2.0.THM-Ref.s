%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hMdoKDqbvW

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:57 EST 2020

% Result     : Theorem 11.98s
% Output     : Refutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 654 expanded)
%              Number of leaves         :   26 ( 194 expanded)
%              Depth                    :   36
%              Number of atoms          : 3014 (11135 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('31',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) ) ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('40',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('43',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

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

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','50'])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('56',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('59',plain,
    ( ( ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X28 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','81'])).

thf('83',plain,
    ( ( ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('96',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X21 @ X20 )
       != X20 )
      | ( v3_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('97',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 )
        | ( ( k1_tops_1 @ X21 @ X20 )
         != X20 )
        | ( v3_pre_topc @ X20 @ X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 )
        | ( ( k1_tops_1 @ X21 @ X20 )
         != X20 )
        | ( v3_pre_topc @ X20 @ X21 ) ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ~ ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 )
        | ( ( k1_tops_1 @ X21 @ X20 )
         != X20 )
        | ( v3_pre_topc @ X20 @ X21 ) )
    | ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf('104',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( ( k1_tops_1 @ X21 @ X20 )
       != X20 )
      | ( v3_pre_topc @ X20 @ X21 ) ) ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( ( k1_tops_1 @ X21 @ X20 )
       != X20 )
      | ( v3_pre_topc @ X20 @ X21 ) ) ),
    inference(simpl_trail,[status(thm)],['97','104'])).

thf('106',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( sk_B != sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','109'])).

thf('111',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
      & ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X29 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['112'])).

thf('114',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_1 @ X28 ) @ sk_A @ X28 ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_1 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X28 @ sk_B )
          | ( r1_tarski @ ( sk_D_1 @ X28 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X29 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['112'])).

thf('116',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['118'])).

thf('120',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['116'])).

thf('121',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['118'])).

thf('122',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('125',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) ) ),
    inference(split,[status(esa)],['124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['124'])).

thf('128',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ~ ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
    | ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['124'])).

thf('133',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference(simpl_trail,[status(thm)],['125','133'])).

thf('135',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['123','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_tops_1 @ X23 @ X24 ) )
      | ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['112'])).

thf('152',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X29 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','154'])).

thf('156',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X29 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X29 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['149','155'])).

thf('157',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','114','115','117','119','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hMdoKDqbvW
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.98/12.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.98/12.20  % Solved by: fo/fo7.sh
% 11.98/12.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.98/12.20  % done 10172 iterations in 11.736s
% 11.98/12.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.98/12.20  % SZS output start Refutation
% 11.98/12.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.98/12.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 11.98/12.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.98/12.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 11.98/12.20  thf(sk_B_type, type, sk_B: $i).
% 11.98/12.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.98/12.20  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 11.98/12.20  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 11.98/12.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.98/12.20  thf(sk_A_type, type, sk_A: $i).
% 11.98/12.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.98/12.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 11.98/12.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.98/12.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 11.98/12.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.98/12.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 11.98/12.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 11.98/12.20  thf(t9_connsp_2, conjecture,
% 11.98/12.20    (![A:$i]:
% 11.98/12.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.98/12.20       ( ![B:$i]:
% 11.98/12.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20           ( ( v3_pre_topc @ B @ A ) <=>
% 11.98/12.20             ( ![C:$i]:
% 11.98/12.20               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.98/12.20                 ( ~( ( r2_hidden @ C @ B ) & 
% 11.98/12.20                      ( ![D:$i]:
% 11.98/12.20                        ( ( m1_subset_1 @
% 11.98/12.20                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 11.98/12.20                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 11.98/12.20  thf(zf_stmt_0, negated_conjecture,
% 11.98/12.20    (~( ![A:$i]:
% 11.98/12.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 11.98/12.20            ( l1_pre_topc @ A ) ) =>
% 11.98/12.20          ( ![B:$i]:
% 11.98/12.20            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20              ( ( v3_pre_topc @ B @ A ) <=>
% 11.98/12.20                ( ![C:$i]:
% 11.98/12.20                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.98/12.20                    ( ~( ( r2_hidden @ C @ B ) & 
% 11.98/12.20                         ( ![D:$i]:
% 11.98/12.20                           ( ( m1_subset_1 @
% 11.98/12.20                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 11.98/12.20                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 11.98/12.20    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 11.98/12.20  thf('0', plain,
% 11.98/12.20      (![X28 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20          | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20          | (r1_tarski @ (sk_D_1 @ X28) @ sk_B)
% 11.98/12.20          | (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('1', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) | 
% 11.98/12.20       ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['0'])).
% 11.98/12.20  thf('2', plain,
% 11.98/12.20      (![X28 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20          | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20          | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28)
% 11.98/12.20          | (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('3', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) | 
% 11.98/12.20       ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['2'])).
% 11.98/12.20  thf('4', plain,
% 11.98/12.20      (![X28 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20          | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20          | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20          | (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('5', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 11.98/12.20       ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['4'])).
% 11.98/12.20  thf('6', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf(d3_tarski, axiom,
% 11.98/12.20    (![A:$i,B:$i]:
% 11.98/12.20     ( ( r1_tarski @ A @ B ) <=>
% 11.98/12.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 11.98/12.20  thf('7', plain,
% 11.98/12.20      (![X1 : $i, X3 : $i]:
% 11.98/12.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('8', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf(t44_tops_1, axiom,
% 11.98/12.20    (![A:$i]:
% 11.98/12.20     ( ( l1_pre_topc @ A ) =>
% 11.98/12.20       ( ![B:$i]:
% 11.98/12.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 11.98/12.20  thf('9', plain,
% 11.98/12.20      (![X13 : $i, X14 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 11.98/12.20          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 11.98/12.20          | ~ (l1_pre_topc @ X14))),
% 11.98/12.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 11.98/12.20  thf('10', plain,
% 11.98/12.20      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['8', '9'])).
% 11.98/12.20  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 11.98/12.20      inference('demod', [status(thm)], ['10', '11'])).
% 11.98/12.20  thf('13', plain,
% 11.98/12.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.98/12.20         (~ (r2_hidden @ X0 @ X1)
% 11.98/12.20          | (r2_hidden @ X0 @ X2)
% 11.98/12.20          | ~ (r1_tarski @ X1 @ X2))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('14', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((r2_hidden @ X0 @ sk_B)
% 11.98/12.20          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['12', '13'])).
% 11.98/12.20  thf('15', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 11.98/12.20          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['7', '14'])).
% 11.98/12.20  thf('16', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf(t3_subset, axiom,
% 11.98/12.20    (![A:$i,B:$i]:
% 11.98/12.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.98/12.20  thf('17', plain,
% 11.98/12.20      (![X10 : $i, X11 : $i]:
% 11.98/12.20         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 11.98/12.20      inference('cnf', [status(esa)], [t3_subset])).
% 11.98/12.20  thf('18', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.98/12.20      inference('sup-', [status(thm)], ['16', '17'])).
% 11.98/12.20  thf('19', plain,
% 11.98/12.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.98/12.20         (~ (r2_hidden @ X0 @ X1)
% 11.98/12.20          | (r2_hidden @ X0 @ X2)
% 11.98/12.20          | ~ (r1_tarski @ X1 @ X2))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('20', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['18', '19'])).
% 11.98/12.20  thf('21', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 11.98/12.20          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 11.98/12.20             (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['15', '20'])).
% 11.98/12.20  thf('22', plain,
% 11.98/12.20      (![X1 : $i, X3 : $i]:
% 11.98/12.20         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('23', plain,
% 11.98/12.20      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 11.98/12.20        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['21', '22'])).
% 11.98/12.20  thf('24', plain,
% 11.98/12.20      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 11.98/12.20      inference('simplify', [status(thm)], ['23'])).
% 11.98/12.20  thf('25', plain,
% 11.98/12.20      (![X10 : $i, X12 : $i]:
% 11.98/12.20         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 11.98/12.20      inference('cnf', [status(esa)], [t3_subset])).
% 11.98/12.20  thf('26', plain,
% 11.98/12.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 11.98/12.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['24', '25'])).
% 11.98/12.20  thf(t7_subset_1, axiom,
% 11.98/12.20    (![A:$i,B:$i]:
% 11.98/12.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 11.98/12.20       ( ![C:$i]:
% 11.98/12.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 11.98/12.20           ( ( ![D:$i]:
% 11.98/12.20               ( ( m1_subset_1 @ D @ A ) =>
% 11.98/12.20                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 11.98/12.20             ( r1_tarski @ B @ C ) ) ) ) ))).
% 11.98/12.20  thf('27', plain,
% 11.98/12.20      (![X7 : $i, X8 : $i, X9 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 11.98/12.20          | (r1_tarski @ X9 @ X7)
% 11.98/12.20          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 11.98/12.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 11.98/12.20      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.98/12.20  thf('28', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20          | (m1_subset_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20             (u1_struct_0 @ sk_A))
% 11.98/12.20          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['26', '27'])).
% 11.98/12.20  thf('29', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (m1_subset_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['6', '28'])).
% 11.98/12.20  thf('30', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (m1_subset_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['6', '28'])).
% 11.98/12.20  thf('31', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))))),
% 11.98/12.20      inference('split', [status(esa)], ['2'])).
% 11.98/12.20  thf('32', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (m1_connsp_2 @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            sk_A @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         | ~ (r2_hidden @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20              sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['30', '31'])).
% 11.98/12.20  thf('33', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('34', plain,
% 11.98/12.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 11.98/12.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['24', '25'])).
% 11.98/12.20  thf('35', plain,
% 11.98/12.20      (![X7 : $i, X8 : $i, X9 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 11.98/12.20          | (r1_tarski @ X9 @ X7)
% 11.98/12.20          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 11.98/12.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 11.98/12.20      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.98/12.20  thf('36', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20          | (r2_hidden @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20             X0)
% 11.98/12.20          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['34', '35'])).
% 11.98/12.20  thf('37', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (r2_hidden @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['33', '36'])).
% 11.98/12.20  thf('38', plain,
% 11.98/12.20      ((((m1_connsp_2 @ 
% 11.98/12.20          (sk_D_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20          sk_A @ 
% 11.98/12.20          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))))),
% 11.98/12.20      inference('clc', [status(thm)], ['32', '37'])).
% 11.98/12.20  thf('39', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (m1_subset_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['6', '28'])).
% 11.98/12.20  thf('40', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('split', [status(esa)], ['4'])).
% 11.98/12.20  thf('41', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (m1_subset_1 @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         | ~ (r2_hidden @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20              sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['39', '40'])).
% 11.98/12.20  thf('42', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (r2_hidden @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['33', '36'])).
% 11.98/12.20  thf('43', plain,
% 11.98/12.20      ((((m1_subset_1 @ 
% 11.98/12.20          (sk_D_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('clc', [status(thm)], ['41', '42'])).
% 11.98/12.20  thf(d1_connsp_2, axiom,
% 11.98/12.20    (![A:$i]:
% 11.98/12.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.98/12.20       ( ![B:$i]:
% 11.98/12.20         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.98/12.20           ( ![C:$i]:
% 11.98/12.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 11.98/12.20                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 11.98/12.20  thf('44', plain,
% 11.98/12.20      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 11.98/12.20          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 11.98/12.20          | (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 11.98/12.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 11.98/12.20          | ~ (l1_pre_topc @ X23)
% 11.98/12.20          | ~ (v2_pre_topc @ X23)
% 11.98/12.20          | (v2_struct_0 @ X23))),
% 11.98/12.20      inference('cnf', [status(esa)], [d1_connsp_2])).
% 11.98/12.20  thf('45', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | (v2_struct_0 @ sk_A)
% 11.98/12.20           | ~ (v2_pre_topc @ sk_A)
% 11.98/12.20           | ~ (l1_pre_topc @ sk_A)
% 11.98/12.20           | (r2_hidden @ X0 @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20           | ~ (m1_connsp_2 @ 
% 11.98/12.20                (sk_D_1 @ 
% 11.98/12.20                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                  (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20                sk_A @ X0)
% 11.98/12.20           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['43', '44'])).
% 11.98/12.20  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('48', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | (v2_struct_0 @ sk_A)
% 11.98/12.20           | (r2_hidden @ X0 @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20           | ~ (m1_connsp_2 @ 
% 11.98/12.20                (sk_D_1 @ 
% 11.98/12.20                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                  (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20                sk_A @ X0)
% 11.98/12.20           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('demod', [status(thm)], ['45', '46', '47'])).
% 11.98/12.20  thf('49', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | ~ (m1_subset_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20              (u1_struct_0 @ sk_A))
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         | (v2_struct_0 @ sk_A)
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['38', '48'])).
% 11.98/12.20  thf('50', plain,
% 11.98/12.20      ((((v2_struct_0 @ sk_A)
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         | ~ (m1_subset_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20              (u1_struct_0 @ sk_A))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['49'])).
% 11.98/12.20  thf('51', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         | (v2_struct_0 @ sk_A)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['29', '50'])).
% 11.98/12.20  thf('52', plain,
% 11.98/12.20      ((((v2_struct_0 @ sk_A)
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['51'])).
% 11.98/12.20  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('54', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('clc', [status(thm)], ['52', '53'])).
% 11.98/12.20  thf('55', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (m1_subset_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['6', '28'])).
% 11.98/12.20  thf('56', plain,
% 11.98/12.20      ((![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (r1_tarski @ (sk_D_1 @ X28) @ sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('split', [status(esa)], ['0'])).
% 11.98/12.20  thf('57', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            sk_B)
% 11.98/12.20         | ~ (r2_hidden @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20              sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['55', '56'])).
% 11.98/12.20  thf('58', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | (r2_hidden @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20           sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['33', '36'])).
% 11.98/12.20  thf('59', plain,
% 11.98/12.20      ((((r1_tarski @ 
% 11.98/12.20          (sk_D_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20          sk_B)
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('clc', [status(thm)], ['57', '58'])).
% 11.98/12.20  thf('60', plain,
% 11.98/12.20      (![X1 : $i, X3 : $i]:
% 11.98/12.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('61', plain,
% 11.98/12.20      ((((r1_tarski @ 
% 11.98/12.20          (sk_D_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20          sk_B)
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('clc', [status(thm)], ['57', '58'])).
% 11.98/12.20  thf('62', plain,
% 11.98/12.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.98/12.20         (~ (r2_hidden @ X0 @ X1)
% 11.98/12.20          | (r2_hidden @ X0 @ X2)
% 11.98/12.20          | ~ (r1_tarski @ X1 @ X2))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('63', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | (r2_hidden @ X0 @ sk_B)
% 11.98/12.20           | ~ (r2_hidden @ X0 @ 
% 11.98/12.20                (sk_D_1 @ 
% 11.98/12.20                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                  (u1_struct_0 @ sk_A))))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['61', '62'])).
% 11.98/12.20  thf('64', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            X0)
% 11.98/12.20           | (r2_hidden @ 
% 11.98/12.20              (sk_C @ X0 @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20              sk_B)
% 11.98/12.20           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['60', '63'])).
% 11.98/12.20  thf('65', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['18', '19'])).
% 11.98/12.20  thf('66', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | (r1_tarski @ 
% 11.98/12.20              (sk_D_1 @ 
% 11.98/12.20               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20              X0)
% 11.98/12.20           | (r2_hidden @ 
% 11.98/12.20              (sk_C @ X0 @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20              (u1_struct_0 @ sk_A))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['64', '65'])).
% 11.98/12.20  thf('67', plain,
% 11.98/12.20      (![X1 : $i, X3 : $i]:
% 11.98/12.20         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('68', plain,
% 11.98/12.20      ((((r1_tarski @ 
% 11.98/12.20          (sk_D_1 @ 
% 11.98/12.20           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20          (u1_struct_0 @ sk_A))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            (u1_struct_0 @ sk_A))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['66', '67'])).
% 11.98/12.20  thf('69', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            (u1_struct_0 @ sk_A))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['68'])).
% 11.98/12.20  thf('70', plain,
% 11.98/12.20      (![X10 : $i, X12 : $i]:
% 11.98/12.20         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 11.98/12.20      inference('cnf', [status(esa)], [t3_subset])).
% 11.98/12.20  thf('71', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (m1_subset_1 @ 
% 11.98/12.20            (sk_D_1 @ 
% 11.98/12.20             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['69', '70'])).
% 11.98/12.20  thf(t48_tops_1, axiom,
% 11.98/12.20    (![A:$i]:
% 11.98/12.20     ( ( l1_pre_topc @ A ) =>
% 11.98/12.20       ( ![B:$i]:
% 11.98/12.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20           ( ![C:$i]:
% 11.98/12.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20               ( ( r1_tarski @ B @ C ) =>
% 11.98/12.20                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 11.98/12.20  thf('72', plain,
% 11.98/12.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 11.98/12.20          | ~ (r1_tarski @ X15 @ X17)
% 11.98/12.20          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 11.98/12.20          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 11.98/12.20          | ~ (l1_pre_topc @ X16))),
% 11.98/12.20      inference('cnf', [status(esa)], [t48_tops_1])).
% 11.98/12.20  thf('73', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | ~ (l1_pre_topc @ sk_A)
% 11.98/12.20           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20           | (r1_tarski @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ X0))
% 11.98/12.20           | ~ (r1_tarski @ 
% 11.98/12.20                (sk_D_1 @ 
% 11.98/12.20                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                  (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20                X0)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['71', '72'])).
% 11.98/12.20  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('75', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20           | (r1_tarski @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ 
% 11.98/12.20               (sk_D_1 @ 
% 11.98/12.20                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20              (k1_tops_1 @ sk_A @ X0))
% 11.98/12.20           | ~ (r1_tarski @ 
% 11.98/12.20                (sk_D_1 @ 
% 11.98/12.20                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                  (u1_struct_0 @ sk_A))) @ 
% 11.98/12.20                X0)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('demod', [status(thm)], ['73', '74'])).
% 11.98/12.20  thf('76', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['59', '75'])).
% 11.98/12.20  thf('77', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('78', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ 
% 11.98/12.20             (sk_D_1 @ 
% 11.98/12.20              (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('demod', [status(thm)], ['76', '77'])).
% 11.98/12.20  thf('79', plain,
% 11.98/12.20      ((((r1_tarski @ 
% 11.98/12.20          (k1_tops_1 @ sk_A @ 
% 11.98/12.20           (sk_D_1 @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 11.98/12.20          (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['78'])).
% 11.98/12.20  thf('80', plain,
% 11.98/12.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.98/12.20         (~ (r2_hidden @ X0 @ X1)
% 11.98/12.20          | (r2_hidden @ X0 @ X2)
% 11.98/12.20          | ~ (r1_tarski @ X1 @ X2))),
% 11.98/12.20      inference('cnf', [status(esa)], [d3_tarski])).
% 11.98/12.20  thf('81', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20           | ~ (r2_hidden @ X0 @ 
% 11.98/12.20                (k1_tops_1 @ sk_A @ 
% 11.98/12.20                 (sk_D_1 @ 
% 11.98/12.20                  (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 11.98/12.20                   (u1_struct_0 @ sk_A)))))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['79', '80'])).
% 11.98/12.20  thf('82', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r2_hidden @ 
% 11.98/12.20            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20            (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['54', '81'])).
% 11.98/12.20  thf('83', plain,
% 11.98/12.20      ((((r2_hidden @ 
% 11.98/12.20          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20          (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['82'])).
% 11.98/12.20  thf('84', plain,
% 11.98/12.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 11.98/12.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['24', '25'])).
% 11.98/12.20  thf('85', plain,
% 11.98/12.20      (![X7 : $i, X8 : $i, X9 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 11.98/12.20          | (r1_tarski @ X9 @ X7)
% 11.98/12.20          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 11.98/12.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 11.98/12.20      inference('cnf', [status(esa)], [t7_subset_1])).
% 11.98/12.20  thf('86', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20          | ~ (r2_hidden @ 
% 11.98/12.20               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 11.98/12.20               (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['84', '85'])).
% 11.98/12.20  thf('87', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['83', '86'])).
% 11.98/12.20  thf('88', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('89', plain,
% 11.98/12.20      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('demod', [status(thm)], ['87', '88'])).
% 11.98/12.20  thf('90', plain,
% 11.98/12.20      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['89'])).
% 11.98/12.20  thf('91', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 11.98/12.20      inference('demod', [status(thm)], ['10', '11'])).
% 11.98/12.20  thf(d10_xboole_0, axiom,
% 11.98/12.20    (![A:$i,B:$i]:
% 11.98/12.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.98/12.20  thf('92', plain,
% 11.98/12.20      (![X4 : $i, X6 : $i]:
% 11.98/12.20         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 11.98/12.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.98/12.20  thf('93', plain,
% 11.98/12.20      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['91', '92'])).
% 11.98/12.20  thf('94', plain,
% 11.98/12.20      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['90', '93'])).
% 11.98/12.20  thf('95', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf(t55_tops_1, axiom,
% 11.98/12.20    (![A:$i]:
% 11.98/12.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 11.98/12.20       ( ![B:$i]:
% 11.98/12.20         ( ( l1_pre_topc @ B ) =>
% 11.98/12.20           ( ![C:$i]:
% 11.98/12.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 11.98/12.20               ( ![D:$i]:
% 11.98/12.20                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 11.98/12.20                   ( ( ( v3_pre_topc @ D @ B ) =>
% 11.98/12.20                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 11.98/12.20                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 11.98/12.20                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 11.98/12.20  thf('96', plain,
% 11.98/12.20      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 11.98/12.20         (~ (l1_pre_topc @ X18)
% 11.98/12.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20          | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20          | (v3_pre_topc @ X20 @ X21)
% 11.98/12.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20          | ~ (l1_pre_topc @ X21)
% 11.98/12.20          | ~ (v2_pre_topc @ X21))),
% 11.98/12.20      inference('cnf', [status(esa)], [t55_tops_1])).
% 11.98/12.20  thf('97', plain,
% 11.98/12.20      ((![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)
% 11.98/12.20           | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20           | (v3_pre_topc @ X20 @ X21)))
% 11.98/12.20         <= ((![X20 : $i, X21 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20                 | ~ (l1_pre_topc @ X21)
% 11.98/12.20                 | ~ (v2_pre_topc @ X21)
% 11.98/12.20                 | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20                 | (v3_pre_topc @ X20 @ X21))))),
% 11.98/12.20      inference('split', [status(esa)], ['96'])).
% 11.98/12.20  thf('98', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('99', plain,
% 11.98/12.20      ((![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))))
% 11.98/12.20         <= ((![X18 : $i, X19 : $i]:
% 11.98/12.20                (~ (l1_pre_topc @ X18)
% 11.98/12.20                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))))),
% 11.98/12.20      inference('split', [status(esa)], ['96'])).
% 11.98/12.20  thf('100', plain,
% 11.98/12.20      ((~ (l1_pre_topc @ sk_A))
% 11.98/12.20         <= ((![X18 : $i, X19 : $i]:
% 11.98/12.20                (~ (l1_pre_topc @ X18)
% 11.98/12.20                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['98', '99'])).
% 11.98/12.20  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('102', plain,
% 11.98/12.20      (~
% 11.98/12.20       (![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))))),
% 11.98/12.20      inference('demod', [status(thm)], ['100', '101'])).
% 11.98/12.20  thf('103', plain,
% 11.98/12.20      ((![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)
% 11.98/12.20           | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20           | (v3_pre_topc @ X20 @ X21))) | 
% 11.98/12.20       (![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))))),
% 11.98/12.20      inference('split', [status(esa)], ['96'])).
% 11.98/12.20  thf('104', plain,
% 11.98/12.20      ((![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)
% 11.98/12.20           | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20           | (v3_pre_topc @ X20 @ X21)))),
% 11.98/12.20      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 11.98/12.20  thf('105', plain,
% 11.98/12.20      (![X20 : $i, X21 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20          | ~ (l1_pre_topc @ X21)
% 11.98/12.20          | ~ (v2_pre_topc @ X21)
% 11.98/12.20          | ((k1_tops_1 @ X21 @ X20) != (X20))
% 11.98/12.20          | (v3_pre_topc @ X20 @ X21))),
% 11.98/12.20      inference('simpl_trail', [status(thm)], ['97', '104'])).
% 11.98/12.20  thf('106', plain,
% 11.98/12.20      (((v3_pre_topc @ sk_B @ sk_A)
% 11.98/12.20        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 11.98/12.20        | ~ (v2_pre_topc @ sk_A)
% 11.98/12.20        | ~ (l1_pre_topc @ sk_A))),
% 11.98/12.20      inference('sup-', [status(thm)], ['95', '105'])).
% 11.98/12.20  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('109', plain,
% 11.98/12.20      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 11.98/12.20      inference('demod', [status(thm)], ['106', '107', '108'])).
% 11.98/12.20  thf('110', plain,
% 11.98/12.20      (((((sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A)))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['94', '109'])).
% 11.98/12.20  thf('111', plain,
% 11.98/12.20      (((v3_pre_topc @ sk_B @ sk_A))
% 11.98/12.20         <= ((![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) & 
% 11.98/12.20             (![X28 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20                 | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20                 | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 11.98/12.20      inference('simplify', [status(thm)], ['110'])).
% 11.98/12.20  thf('112', plain,
% 11.98/12.20      (![X29 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20          | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20          | ~ (r1_tarski @ X29 @ sk_B)
% 11.98/12.20          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('113', plain,
% 11.98/12.20      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 11.98/12.20      inference('split', [status(esa)], ['112'])).
% 11.98/12.20  thf('114', plain,
% 11.98/12.20      (~
% 11.98/12.20       (![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_connsp_2 @ (sk_D_1 @ X28) @ sk_A @ X28))) | 
% 11.98/12.20       ~
% 11.98/12.20       (![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (m1_subset_1 @ (sk_D_1 @ X28) @ 
% 11.98/12.20              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 11.98/12.20       ~
% 11.98/12.20       (![X28 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | ~ (r2_hidden @ X28 @ sk_B)
% 11.98/12.20           | (r1_tarski @ (sk_D_1 @ X28) @ sk_B))) | 
% 11.98/12.20       ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('sup-', [status(thm)], ['111', '113'])).
% 11.98/12.20  thf('115', plain,
% 11.98/12.20      ((![X29 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20           | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20           | ~ (r1_tarski @ X29 @ sk_B))) | 
% 11.98/12.20       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['112'])).
% 11.98/12.20  thf('116', plain,
% 11.98/12.20      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('117', plain,
% 11.98/12.20      (((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['116'])).
% 11.98/12.20  thf('118', plain,
% 11.98/12.20      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 11.98/12.20        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('119', plain,
% 11.98/12.20      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))) | 
% 11.98/12.20       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('split', [status(esa)], ['118'])).
% 11.98/12.20  thf('120', plain,
% 11.98/12.20      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 11.98/12.20      inference('split', [status(esa)], ['116'])).
% 11.98/12.20  thf('121', plain,
% 11.98/12.20      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20         <= (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 11.98/12.20      inference('split', [status(esa)], ['118'])).
% 11.98/12.20  thf('122', plain,
% 11.98/12.20      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.98/12.20      inference('split', [status(esa)], ['0'])).
% 11.98/12.20  thf('123', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('124', plain,
% 11.98/12.20      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 11.98/12.20         (~ (l1_pre_topc @ X18)
% 11.98/12.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20          | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20          | ((k1_tops_1 @ X18 @ X19) = (X19))
% 11.98/12.20          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20          | ~ (l1_pre_topc @ X21)
% 11.98/12.20          | ~ (v2_pre_topc @ X21))),
% 11.98/12.20      inference('cnf', [status(esa)], [t55_tops_1])).
% 11.98/12.20  thf('125', plain,
% 11.98/12.20      ((![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20           | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20           | ((k1_tops_1 @ X18 @ X19) = (X19))))
% 11.98/12.20         <= ((![X18 : $i, X19 : $i]:
% 11.98/12.20                (~ (l1_pre_topc @ X18)
% 11.98/12.20                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20                 | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20                 | ((k1_tops_1 @ X18 @ X19) = (X19)))))),
% 11.98/12.20      inference('split', [status(esa)], ['124'])).
% 11.98/12.20  thf('126', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('127', plain,
% 11.98/12.20      ((![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)))
% 11.98/12.20         <= ((![X20 : $i, X21 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20                 | ~ (l1_pre_topc @ X21)
% 11.98/12.20                 | ~ (v2_pre_topc @ X21))))),
% 11.98/12.20      inference('split', [status(esa)], ['124'])).
% 11.98/12.20  thf('128', plain,
% 11.98/12.20      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 11.98/12.20         <= ((![X20 : $i, X21 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20                 | ~ (l1_pre_topc @ X21)
% 11.98/12.20                 | ~ (v2_pre_topc @ X21))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['126', '127'])).
% 11.98/12.20  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('131', plain,
% 11.98/12.20      (~
% 11.98/12.20       (![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)))),
% 11.98/12.20      inference('demod', [status(thm)], ['128', '129', '130'])).
% 11.98/12.20  thf('132', plain,
% 11.98/12.20      ((![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20           | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20           | ((k1_tops_1 @ X18 @ X19) = (X19)))) | 
% 11.98/12.20       (![X20 : $i, X21 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 11.98/12.20           | ~ (l1_pre_topc @ X21)
% 11.98/12.20           | ~ (v2_pre_topc @ X21)))),
% 11.98/12.20      inference('split', [status(esa)], ['124'])).
% 11.98/12.20  thf('133', plain,
% 11.98/12.20      ((![X18 : $i, X19 : $i]:
% 11.98/12.20          (~ (l1_pre_topc @ X18)
% 11.98/12.20           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20           | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20           | ((k1_tops_1 @ X18 @ X19) = (X19))))),
% 11.98/12.20      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 11.98/12.20  thf('134', plain,
% 11.98/12.20      (![X18 : $i, X19 : $i]:
% 11.98/12.20         (~ (l1_pre_topc @ X18)
% 11.98/12.20          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 11.98/12.20          | ~ (v3_pre_topc @ X19 @ X18)
% 11.98/12.20          | ((k1_tops_1 @ X18 @ X19) = (X19)))),
% 11.98/12.20      inference('simpl_trail', [status(thm)], ['125', '133'])).
% 11.98/12.20  thf('135', plain,
% 11.98/12.20      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 11.98/12.20        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 11.98/12.20        | ~ (l1_pre_topc @ sk_A))),
% 11.98/12.20      inference('sup-', [status(thm)], ['123', '134'])).
% 11.98/12.20  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('137', plain,
% 11.98/12.20      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 11.98/12.20      inference('demod', [status(thm)], ['135', '136'])).
% 11.98/12.20  thf('138', plain,
% 11.98/12.20      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 11.98/12.20         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['122', '137'])).
% 11.98/12.20  thf('139', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('140', plain,
% 11.98/12.20      (![X22 : $i, X23 : $i, X24 : $i]:
% 11.98/12.20         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 11.98/12.20          | ~ (r2_hidden @ X22 @ (k1_tops_1 @ X23 @ X24))
% 11.98/12.20          | (m1_connsp_2 @ X24 @ X23 @ X22)
% 11.98/12.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 11.98/12.20          | ~ (l1_pre_topc @ X23)
% 11.98/12.20          | ~ (v2_pre_topc @ X23)
% 11.98/12.20          | (v2_struct_0 @ X23))),
% 11.98/12.20      inference('cnf', [status(esa)], [d1_connsp_2])).
% 11.98/12.20  thf('141', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((v2_struct_0 @ sk_A)
% 11.98/12.20          | ~ (v2_pre_topc @ sk_A)
% 11.98/12.20          | ~ (l1_pre_topc @ sk_A)
% 11.98/12.20          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 11.98/12.20          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['139', '140'])).
% 11.98/12.20  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('144', plain,
% 11.98/12.20      (![X0 : $i]:
% 11.98/12.20         ((v2_struct_0 @ sk_A)
% 11.98/12.20          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 11.98/12.20          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 11.98/12.20          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('demod', [status(thm)], ['141', '142', '143'])).
% 11.98/12.20  thf('145', plain,
% 11.98/12.20      ((![X0 : $i]:
% 11.98/12.20          (~ (r2_hidden @ X0 @ sk_B)
% 11.98/12.20           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.98/12.20           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 11.98/12.20           | (v2_struct_0 @ sk_A)))
% 11.98/12.20         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 11.98/12.20      inference('sup-', [status(thm)], ['138', '144'])).
% 11.98/12.20  thf('146', plain,
% 11.98/12.20      ((((v2_struct_0 @ sk_A)
% 11.98/12.20         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 11.98/12.20         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 11.98/12.20         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 11.98/12.20             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['121', '145'])).
% 11.98/12.20  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('148', plain,
% 11.98/12.20      (((~ (r2_hidden @ sk_C_1 @ sk_B) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 11.98/12.20         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 11.98/12.20             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 11.98/12.20      inference('clc', [status(thm)], ['146', '147'])).
% 11.98/12.20  thf('149', plain,
% 11.98/12.20      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 11.98/12.20         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 11.98/12.20             ((r2_hidden @ sk_C_1 @ sk_B)) & 
% 11.98/12.20             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['120', '148'])).
% 11.98/12.20  thf('150', plain,
% 11.98/12.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 11.98/12.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.98/12.20  thf('151', plain,
% 11.98/12.20      ((![X29 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20           | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20           | ~ (r1_tarski @ X29 @ sk_B)))
% 11.98/12.20         <= ((![X29 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20                 | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 11.98/12.20      inference('split', [status(esa)], ['112'])).
% 11.98/12.20  thf('152', plain,
% 11.98/12.20      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 11.98/12.20         <= ((![X29 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20                 | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 11.98/12.20      inference('sup-', [status(thm)], ['150', '151'])).
% 11.98/12.20  thf('153', plain,
% 11.98/12.20      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 11.98/12.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 11.98/12.20  thf('154', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 11.98/12.20      inference('simplify', [status(thm)], ['153'])).
% 11.98/12.20  thf('155', plain,
% 11.98/12.20      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 11.98/12.20         <= ((![X29 : $i]:
% 11.98/12.20                (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20                 | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20                 | ~ (r1_tarski @ X29 @ sk_B))))),
% 11.98/12.20      inference('demod', [status(thm)], ['152', '154'])).
% 11.98/12.20  thf('156', plain,
% 11.98/12.20      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 11.98/12.20       ~
% 11.98/12.20       (![X29 : $i]:
% 11.98/12.20          (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 11.98/12.20           | ~ (m1_connsp_2 @ X29 @ sk_A @ sk_C_1)
% 11.98/12.20           | ~ (r1_tarski @ X29 @ sk_B))) | 
% 11.98/12.20       ~ ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))) | 
% 11.98/12.20       ~ ((r2_hidden @ sk_C_1 @ sk_B))),
% 11.98/12.20      inference('sup-', [status(thm)], ['149', '155'])).
% 11.98/12.20  thf('157', plain, ($false),
% 11.98/12.20      inference('sat_resolution*', [status(thm)],
% 11.98/12.20                ['1', '3', '5', '114', '115', '117', '119', '156'])).
% 11.98/12.20  
% 11.98/12.20  % SZS output end Refutation
% 11.98/12.20  
% 11.98/12.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
