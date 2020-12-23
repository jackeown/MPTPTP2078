%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuJzbwrvHZ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:57 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 796 expanded)
%              Number of leaves         :   27 ( 220 expanded)
%              Depth                    :   32
%              Number of atoms          : 2023 (13934 expanded)
%              Number of equality atoms :   17 ( 113 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
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
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('23',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('26',plain,
    ( ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( l1_pre_topc @ X20 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( v3_pre_topc @ X21 @ X20 )
        | ( ( k1_tops_1 @ X20 @ X21 )
          = X21 ) )
    | ! [X22: $i,X23: $i] :
        ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
        | ~ ( l1_pre_topc @ X23 )
        | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X21 )
        = X21 ) ) ),
    inference(simpl_trail,[status(thm)],['23','32'])).

thf('34',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('54',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X38 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X38 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','55'])).

thf('57',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('60',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_connsp_2 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('103',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','55','106'])).

thf('108',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simpl_trail,[status(thm)],['104','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X37: $i] :
      ( ( m1_connsp_2 @ ( sk_D_1 @ X37 ) @ sk_A @ X37 )
      | ~ ( r2_hidden @ X37 @ sk_B ) ) ),
    inference(clc,[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','112'])).

thf('114',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('115',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','55','118'])).

thf('120',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('122',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X37 @ sk_B ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('143',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X37 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('148',plain,(
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X37 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X37 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','55','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['146','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['141','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('156',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['96','157'])).

thf('159',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['63','158'])).

thf('160',plain,(
    $false ),
    inference(demod,[status(thm)],['57','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuJzbwrvHZ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.74/2.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.74/2.99  % Solved by: fo/fo7.sh
% 2.74/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.74/2.99  % done 3315 iterations in 2.539s
% 2.74/2.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.74/2.99  % SZS output start Refutation
% 2.74/2.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.74/2.99  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 2.74/2.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.74/2.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.74/2.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.74/2.99  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.74/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.74/2.99  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.74/2.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.74/2.99  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 2.74/2.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.74/2.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.74/2.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.74/2.99  thf(sk_B_type, type, sk_B: $i).
% 2.74/2.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.74/2.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.74/2.99  thf(t9_connsp_2, conjecture,
% 2.74/2.99    (![A:$i]:
% 2.74/2.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.74/2.99       ( ![B:$i]:
% 2.74/2.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99           ( ( v3_pre_topc @ B @ A ) <=>
% 2.74/2.99             ( ![C:$i]:
% 2.74/2.99               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.74/2.99                 ( ~( ( r2_hidden @ C @ B ) & 
% 2.74/2.99                      ( ![D:$i]:
% 2.74/2.99                        ( ( m1_subset_1 @
% 2.74/2.99                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 2.74/2.99                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.74/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.74/2.99    (~( ![A:$i]:
% 2.74/2.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.74/2.99            ( l1_pre_topc @ A ) ) =>
% 2.74/2.99          ( ![B:$i]:
% 2.74/2.99            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99              ( ( v3_pre_topc @ B @ A ) <=>
% 2.74/2.99                ( ![C:$i]:
% 2.74/2.99                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.74/2.99                    ( ~( ( r2_hidden @ C @ B ) & 
% 2.74/2.99                         ( ![D:$i]:
% 2.74/2.99                           ( ( m1_subset_1 @
% 2.74/2.99                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 2.74/2.99                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.74/2.99    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 2.74/2.99  thf('0', plain,
% 2.74/2.99      (![X38 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99          | ~ (r1_tarski @ X38 @ sk_B)
% 2.74/2.99          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('1', plain,
% 2.74/2.99      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.74/2.99      inference('split', [status(esa)], ['0'])).
% 2.74/2.99  thf('2', plain,
% 2.74/2.99      ((![X38 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99           | ~ (r1_tarski @ X38 @ sk_B))) | 
% 2.74/2.99       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('split', [status(esa)], ['0'])).
% 2.74/2.99  thf('3', plain,
% 2.74/2.99      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('4', plain,
% 2.74/2.99      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C_1 @ sk_B))),
% 2.74/2.99      inference('split', [status(esa)], ['3'])).
% 2.74/2.99  thf('5', plain,
% 2.74/2.99      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('split', [status(esa)], ['3'])).
% 2.74/2.99  thf('6', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(t3_subset, axiom,
% 2.74/2.99    (![A:$i,B:$i]:
% 2.74/2.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.74/2.99  thf('7', plain,
% 2.74/2.99      (![X7 : $i, X8 : $i]:
% 2.74/2.99         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.74/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.74/2.99  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['6', '7'])).
% 2.74/2.99  thf(d3_tarski, axiom,
% 2.74/2.99    (![A:$i,B:$i]:
% 2.74/2.99     ( ( r1_tarski @ A @ B ) <=>
% 2.74/2.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.74/2.99  thf('9', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.99         (~ (r2_hidden @ X0 @ X1)
% 2.74/2.99          | (r2_hidden @ X0 @ X2)
% 2.74/2.99          | ~ (r1_tarski @ X1 @ X2))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('10', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 2.74/2.99      inference('sup-', [status(thm)], ['8', '9'])).
% 2.74/2.99  thf('11', plain,
% 2.74/2.99      (((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['5', '10'])).
% 2.74/2.99  thf(d10_xboole_0, axiom,
% 2.74/2.99    (![A:$i,B:$i]:
% 2.74/2.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.74/2.99  thf('12', plain,
% 2.74/2.99      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.74/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.99  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.74/2.99      inference('simplify', [status(thm)], ['12'])).
% 2.74/2.99  thf('14', plain,
% 2.74/2.99      (![X7 : $i, X9 : $i]:
% 2.74/2.99         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.99      inference('cnf', [status(esa)], [t3_subset])).
% 2.74/2.99  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['13', '14'])).
% 2.74/2.99  thf(t4_subset, axiom,
% 2.74/2.99    (![A:$i,B:$i,C:$i]:
% 2.74/2.99     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.74/2.99       ( m1_subset_1 @ A @ C ) ))).
% 2.74/2.99  thf('16', plain,
% 2.74/2.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.74/2.99         (~ (r2_hidden @ X10 @ X11)
% 2.74/2.99          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.74/2.99          | (m1_subset_1 @ X10 @ X12))),
% 2.74/2.99      inference('cnf', [status(esa)], [t4_subset])).
% 2.74/2.99  thf('17', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['15', '16'])).
% 2.74/2.99  thf('18', plain,
% 2.74/2.99      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99         <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['11', '17'])).
% 2.74/2.99  thf('19', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)
% 2.74/2.99          | (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('20', plain,
% 2.74/2.99      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.74/2.99      inference('split', [status(esa)], ['19'])).
% 2.74/2.99  thf('21', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(t55_tops_1, axiom,
% 2.74/2.99    (![A:$i]:
% 2.74/2.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.74/2.99       ( ![B:$i]:
% 2.74/2.99         ( ( l1_pre_topc @ B ) =>
% 2.74/2.99           ( ![C:$i]:
% 2.74/2.99             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99               ( ![D:$i]:
% 2.74/2.99                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 2.74/2.99                   ( ( ( v3_pre_topc @ D @ B ) =>
% 2.74/2.99                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 2.74/2.99                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 2.74/2.99                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 2.74/2.99  thf('22', plain,
% 2.74/2.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.74/2.99         (~ (l1_pre_topc @ X20)
% 2.74/2.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99          | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99          | ((k1_tops_1 @ X20 @ X21) = (X21))
% 2.74/2.99          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99          | ~ (l1_pre_topc @ X23)
% 2.74/2.99          | ~ (v2_pre_topc @ X23))),
% 2.74/2.99      inference('cnf', [status(esa)], [t55_tops_1])).
% 2.74/2.99  thf('23', plain,
% 2.74/2.99      ((![X20 : $i, X21 : $i]:
% 2.74/2.99          (~ (l1_pre_topc @ X20)
% 2.74/2.99           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99           | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99           | ((k1_tops_1 @ X20 @ X21) = (X21))))
% 2.74/2.99         <= ((![X20 : $i, X21 : $i]:
% 2.74/2.99                (~ (l1_pre_topc @ X20)
% 2.74/2.99                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99                 | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99                 | ((k1_tops_1 @ X20 @ X21) = (X21)))))),
% 2.74/2.99      inference('split', [status(esa)], ['22'])).
% 2.74/2.99  thf('24', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('25', plain,
% 2.74/2.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.74/2.99         (~ (l1_pre_topc @ X20)
% 2.74/2.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99          | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99          | ((k1_tops_1 @ X20 @ X21) = (X21))
% 2.74/2.99          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99          | ~ (l1_pre_topc @ X23)
% 2.74/2.99          | ~ (v2_pre_topc @ X23))),
% 2.74/2.99      inference('cnf', [status(esa)], [t55_tops_1])).
% 2.74/2.99  thf('26', plain,
% 2.74/2.99      ((![X22 : $i, X23 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99           | ~ (l1_pre_topc @ X23)
% 2.74/2.99           | ~ (v2_pre_topc @ X23)))
% 2.74/2.99         <= ((![X22 : $i, X23 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99                 | ~ (l1_pre_topc @ X23)
% 2.74/2.99                 | ~ (v2_pre_topc @ X23))))),
% 2.74/2.99      inference('split', [status(esa)], ['25'])).
% 2.74/2.99  thf('27', plain,
% 2.74/2.99      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 2.74/2.99         <= ((![X22 : $i, X23 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99                 | ~ (l1_pre_topc @ X23)
% 2.74/2.99                 | ~ (v2_pre_topc @ X23))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['24', '26'])).
% 2.74/2.99  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('30', plain,
% 2.74/2.99      (~
% 2.74/2.99       (![X22 : $i, X23 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99           | ~ (l1_pre_topc @ X23)
% 2.74/2.99           | ~ (v2_pre_topc @ X23)))),
% 2.74/2.99      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.74/2.99  thf('31', plain,
% 2.74/2.99      ((![X20 : $i, X21 : $i]:
% 2.74/2.99          (~ (l1_pre_topc @ X20)
% 2.74/2.99           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99           | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99           | ((k1_tops_1 @ X20 @ X21) = (X21)))) | 
% 2.74/2.99       (![X22 : $i, X23 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 2.74/2.99           | ~ (l1_pre_topc @ X23)
% 2.74/2.99           | ~ (v2_pre_topc @ X23)))),
% 2.74/2.99      inference('split', [status(esa)], ['25'])).
% 2.74/2.99  thf('32', plain,
% 2.74/2.99      ((![X20 : $i, X21 : $i]:
% 2.74/2.99          (~ (l1_pre_topc @ X20)
% 2.74/2.99           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99           | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99           | ((k1_tops_1 @ X20 @ X21) = (X21))))),
% 2.74/2.99      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 2.74/2.99  thf('33', plain,
% 2.74/2.99      (![X20 : $i, X21 : $i]:
% 2.74/2.99         (~ (l1_pre_topc @ X20)
% 2.74/2.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.74/2.99          | ~ (v3_pre_topc @ X21 @ X20)
% 2.74/2.99          | ((k1_tops_1 @ X20 @ X21) = (X21)))),
% 2.74/2.99      inference('simpl_trail', [status(thm)], ['23', '32'])).
% 2.74/2.99  thf('34', plain,
% 2.74/2.99      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 2.74/2.99        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 2.74/2.99        | ~ (l1_pre_topc @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['21', '33'])).
% 2.74/2.99  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('36', plain,
% 2.74/2.99      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('demod', [status(thm)], ['34', '35'])).
% 2.74/2.99  thf('37', plain,
% 2.74/2.99      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 2.74/2.99         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['20', '36'])).
% 2.74/2.99  thf('38', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(d1_connsp_2, axiom,
% 2.74/2.99    (![A:$i]:
% 2.74/2.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.74/2.99       ( ![B:$i]:
% 2.74/2.99         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.74/2.99           ( ![C:$i]:
% 2.74/2.99             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 2.74/2.99                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.74/2.99  thf('39', plain,
% 2.74/2.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 2.74/2.99          | ~ (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 2.74/2.99          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 2.74/2.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 2.74/2.99          | ~ (l1_pre_topc @ X25)
% 2.74/2.99          | ~ (v2_pre_topc @ X25)
% 2.74/2.99          | (v2_struct_0 @ X25))),
% 2.74/2.99      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.74/2.99  thf('40', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | ~ (v2_pre_topc @ sk_A)
% 2.74/2.99          | ~ (l1_pre_topc @ sk_A)
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 2.74/2.99          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['38', '39'])).
% 2.74/2.99  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('43', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 2.74/2.99          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('demod', [status(thm)], ['40', '41', '42'])).
% 2.74/2.99  thf('44', plain,
% 2.74/2.99      ((![X0 : $i]:
% 2.74/2.99          (~ (r2_hidden @ X0 @ sk_B)
% 2.74/2.99           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 2.74/2.99           | (v2_struct_0 @ sk_A)))
% 2.74/2.99         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['37', '43'])).
% 2.74/2.99  thf('45', plain,
% 2.74/2.99      ((((v2_struct_0 @ sk_A)
% 2.74/2.99         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 2.74/2.99         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 2.74/2.99         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['18', '44'])).
% 2.74/2.99  thf('46', plain,
% 2.74/2.99      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('split', [status(esa)], ['3'])).
% 2.74/2.99  thf('47', plain,
% 2.74/2.99      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 2.74/2.99         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('demod', [status(thm)], ['45', '46'])).
% 2.74/2.99  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('49', plain,
% 2.74/2.99      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 2.74/2.99         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C_1 @ sk_B)))),
% 2.74/2.99      inference('clc', [status(thm)], ['47', '48'])).
% 2.74/2.99  thf('50', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('51', plain,
% 2.74/2.99      ((![X38 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99           | ~ (r1_tarski @ X38 @ sk_B)))
% 2.74/2.99         <= ((![X38 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 2.74/2.99      inference('split', [status(esa)], ['0'])).
% 2.74/2.99  thf('52', plain,
% 2.74/2.99      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 2.74/2.99         <= ((![X38 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['50', '51'])).
% 2.74/2.99  thf('53', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.74/2.99      inference('simplify', [status(thm)], ['12'])).
% 2.74/2.99  thf('54', plain,
% 2.74/2.99      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 2.74/2.99         <= ((![X38 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99                 | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99                 | ~ (r1_tarski @ X38 @ sk_B))))),
% 2.74/2.99      inference('demod', [status(thm)], ['52', '53'])).
% 2.74/2.99  thf('55', plain,
% 2.74/2.99      (~ ((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 2.74/2.99       ~
% 2.74/2.99       (![X38 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99           | ~ (m1_connsp_2 @ X38 @ sk_A @ sk_C_1)
% 2.74/2.99           | ~ (r1_tarski @ X38 @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['49', '54'])).
% 2.74/2.99  thf('56', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('sat_resolution*', [status(thm)], ['2', '4', '55'])).
% 2.74/2.99  thf('57', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 2.74/2.99      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 2.74/2.99  thf('58', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(fc9_tops_1, axiom,
% 2.74/2.99    (![A:$i,B:$i]:
% 2.74/2.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.74/2.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.74/2.99       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.74/2.99  thf('59', plain,
% 2.74/2.99      (![X15 : $i, X16 : $i]:
% 2.74/2.99         (~ (l1_pre_topc @ X15)
% 2.74/2.99          | ~ (v2_pre_topc @ X15)
% 2.74/2.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 2.74/2.99          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 2.74/2.99      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.74/2.99  thf('60', plain,
% 2.74/2.99      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 2.74/2.99        | ~ (v2_pre_topc @ sk_A)
% 2.74/2.99        | ~ (l1_pre_topc @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['58', '59'])).
% 2.74/2.99  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('63', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 2.74/2.99      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.74/2.99  thf('64', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('65', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(dt_k1_tops_1, axiom,
% 2.74/2.99    (![A:$i,B:$i]:
% 2.74/2.99     ( ( ( l1_pre_topc @ A ) & 
% 2.74/2.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.74/2.99       ( m1_subset_1 @
% 2.74/2.99         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.74/2.99  thf('66', plain,
% 2.74/2.99      (![X13 : $i, X14 : $i]:
% 2.74/2.99         (~ (l1_pre_topc @ X13)
% 2.74/2.99          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.74/2.99          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 2.74/2.99      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.74/2.99  thf('67', plain,
% 2.74/2.99      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.74/2.99         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99        | ~ (l1_pre_topc @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['65', '66'])).
% 2.74/2.99  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('69', plain,
% 2.74/2.99      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 2.74/2.99        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('demod', [status(thm)], ['67', '68'])).
% 2.74/2.99  thf('70', plain,
% 2.74/2.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.74/2.99         (~ (r2_hidden @ X10 @ X11)
% 2.74/2.99          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.74/2.99          | (m1_subset_1 @ X10 @ X12))),
% 2.74/2.99      inference('cnf', [status(esa)], [t4_subset])).
% 2.74/2.99  thf('71', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['69', '70'])).
% 2.74/2.99  thf('72', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 2.74/2.99             (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['64', '71'])).
% 2.74/2.99  thf('73', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('74', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 2.74/2.99          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('demod', [status(thm)], ['40', '41', '42'])).
% 2.74/2.99  thf('75', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 2.74/2.99               (u1_struct_0 @ sk_A))
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 2.74/2.99             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.74/2.99          | (v2_struct_0 @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['73', '74'])).
% 2.74/2.99  thf('76', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 2.74/2.99             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['72', '75'])).
% 2.74/2.99  thf('77', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((m1_connsp_2 @ sk_B @ sk_A @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.74/2.99      inference('simplify', [status(thm)], ['76'])).
% 2.74/2.99  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('79', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (m1_connsp_2 @ sk_B @ sk_A @ 
% 2.74/2.99             (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.74/2.99      inference('clc', [status(thm)], ['77', '78'])).
% 2.74/2.99  thf('80', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 2.74/2.99             (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['64', '71'])).
% 2.74/2.99  thf('81', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf(t6_connsp_2, axiom,
% 2.74/2.99    (![A:$i]:
% 2.74/2.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.74/2.99       ( ![B:$i]:
% 2.74/2.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99           ( ![C:$i]:
% 2.74/2.99             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.74/2.99               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.74/2.99  thf('82', plain,
% 2.74/2.99      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.74/2.99          | ~ (m1_connsp_2 @ X30 @ X31 @ X32)
% 2.74/2.99          | (r2_hidden @ X32 @ X30)
% 2.74/2.99          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 2.74/2.99          | ~ (l1_pre_topc @ X31)
% 2.74/2.99          | ~ (v2_pre_topc @ X31)
% 2.74/2.99          | (v2_struct_0 @ X31))),
% 2.74/2.99      inference('cnf', [status(esa)], [t6_connsp_2])).
% 2.74/2.99  thf('83', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | ~ (v2_pre_topc @ sk_A)
% 2.74/2.99          | ~ (l1_pre_topc @ sk_A)
% 2.74/2.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | (r2_hidden @ X0 @ sk_B)
% 2.74/2.99          | ~ (m1_connsp_2 @ sk_B @ sk_A @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['81', '82'])).
% 2.74/2.99  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('86', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | (r2_hidden @ X0 @ sk_B)
% 2.74/2.99          | ~ (m1_connsp_2 @ sk_B @ sk_A @ X0))),
% 2.74/2.99      inference('demod', [status(thm)], ['83', '84', '85'])).
% 2.74/2.99  thf('87', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | ~ (m1_connsp_2 @ sk_B @ sk_A @ 
% 2.74/2.99               (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 2.74/2.99          | (v2_struct_0 @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['80', '86'])).
% 2.74/2.99  thf('88', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['79', '87'])).
% 2.74/2.99  thf('89', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 2.74/2.99      inference('simplify', [status(thm)], ['88'])).
% 2.74/2.99  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('91', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B))),
% 2.74/2.99      inference('clc', [status(thm)], ['89', '90'])).
% 2.74/2.99  thf('92', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('93', plain,
% 2.74/2.99      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 2.74/2.99        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.74/2.99      inference('sup-', [status(thm)], ['91', '92'])).
% 2.74/2.99  thf('94', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.74/2.99      inference('simplify', [status(thm)], ['93'])).
% 2.74/2.99  thf('95', plain,
% 2.74/2.99      (![X4 : $i, X6 : $i]:
% 2.74/2.99         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.74/2.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.99  thf('96', plain,
% 2.74/2.99      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['94', '95'])).
% 2.74/2.99  thf('97', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('98', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 2.74/2.99      inference('sup-', [status(thm)], ['8', '9'])).
% 2.74/2.99  thf('99', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['97', '98'])).
% 2.74/2.99  thf('100', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['15', '16'])).
% 2.74/2.99  thf('101', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['99', '100'])).
% 2.74/2.99  thf('102', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('103', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 2.74/2.99          | (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('104', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)))
% 2.74/2.99         <= ((![X37 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99                 | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99                 | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))))),
% 2.74/2.99      inference('split', [status(esa)], ['103'])).
% 2.74/2.99  thf('105', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 2.74/2.99          | (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('106', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))) | 
% 2.74/2.99       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('split', [status(esa)], ['105'])).
% 2.74/2.99  thf('107', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)))),
% 2.74/2.99      inference('sat_resolution*', [status(thm)], ['2', '4', '55', '106'])).
% 2.74/2.99  thf('108', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37))),
% 2.74/2.99      inference('simpl_trail', [status(thm)], ['104', '107'])).
% 2.74/2.99  thf('109', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('110', plain,
% 2.74/2.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.74/2.99         (~ (r2_hidden @ X10 @ X11)
% 2.74/2.99          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.74/2.99          | (m1_subset_1 @ X10 @ X12))),
% 2.74/2.99      inference('cnf', [status(esa)], [t4_subset])).
% 2.74/2.99  thf('111', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 2.74/2.99      inference('sup-', [status(thm)], ['109', '110'])).
% 2.74/2.99  thf('112', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         ((m1_connsp_2 @ (sk_D_1 @ X37) @ sk_A @ X37)
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B))),
% 2.74/2.99      inference('clc', [status(thm)], ['108', '111'])).
% 2.74/2.99  thf('113', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (m1_connsp_2 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A @ 
% 2.74/2.99             (sk_C @ X0 @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['102', '112'])).
% 2.74/2.99  thf('114', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('115', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('116', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.74/2.99         <= ((![X37 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99                 | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99                 | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 2.74/2.99      inference('split', [status(esa)], ['115'])).
% 2.74/2.99  thf('117', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | (v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('118', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 2.74/2.99       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('split', [status(esa)], ['117'])).
% 2.74/2.99  thf('119', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.74/2.99      inference('sat_resolution*', [status(thm)], ['2', '4', '55', '118'])).
% 2.74/2.99  thf('120', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99          | (m1_subset_1 @ (sk_D_1 @ X37) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.74/2.99      inference('simpl_trail', [status(thm)], ['116', '119'])).
% 2.74/2.99  thf('121', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 2.74/2.99      inference('sup-', [status(thm)], ['109', '110'])).
% 2.74/2.99  thf('122', plain,
% 2.74/2.99      (![X37 : $i]:
% 2.74/2.99         ((m1_subset_1 @ (sk_D_1 @ X37) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | ~ (r2_hidden @ X37 @ sk_B))),
% 2.74/2.99      inference('clc', [status(thm)], ['120', '121'])).
% 2.74/2.99  thf('123', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['114', '122'])).
% 2.74/2.99  thf('124', plain,
% 2.74/2.99      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 2.74/2.99          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 2.74/2.99          | (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 2.74/2.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 2.74/2.99          | ~ (l1_pre_topc @ X25)
% 2.74/2.99          | ~ (v2_pre_topc @ X25)
% 2.74/2.99          | (v2_struct_0 @ X25))),
% 2.74/2.99      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.74/2.99  thf('125', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | ~ (v2_pre_topc @ sk_A)
% 2.74/2.99          | ~ (l1_pre_topc @ sk_A)
% 2.74/2.99          | (r2_hidden @ X1 @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | ~ (m1_connsp_2 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 2.74/2.99          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['123', '124'])).
% 2.74/2.99  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('128', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (r2_hidden @ X1 @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | ~ (m1_connsp_2 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_A @ X1)
% 2.74/2.99          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('demod', [status(thm)], ['125', '126', '127'])).
% 2.74/2.99  thf('129', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | (v2_struct_0 @ sk_A)
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['113', '128'])).
% 2.74/2.99  thf('130', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('simplify', [status(thm)], ['129'])).
% 2.74/2.99  thf('131', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | (v2_struct_0 @ sk_A))),
% 2.74/2.99      inference('sup-', [status(thm)], ['101', '130'])).
% 2.74/2.99  thf('132', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((v2_struct_0 @ sk_A)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))))
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('simplify', [status(thm)], ['131'])).
% 2.74/2.99  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('134', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))))),
% 2.74/2.99      inference('clc', [status(thm)], ['132', '133'])).
% 2.74/2.99  thf('135', plain,
% 2.74/2.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('136', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ 
% 2.74/2.99             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['114', '122'])).
% 2.74/2.99  thf(t48_tops_1, axiom,
% 2.74/2.99    (![A:$i]:
% 2.74/2.99     ( ( l1_pre_topc @ A ) =>
% 2.74/2.99       ( ![B:$i]:
% 2.74/2.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99           ( ![C:$i]:
% 2.74/2.99             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.74/2.99               ( ( r1_tarski @ B @ C ) =>
% 2.74/2.99                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.74/2.99  thf('137', plain,
% 2.74/2.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.74/2.99         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.74/2.99          | ~ (r1_tarski @ X17 @ X19)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 2.74/2.99          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.74/2.99          | ~ (l1_pre_topc @ X18))),
% 2.74/2.99      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.74/2.99  thf('138', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | ~ (l1_pre_topc @ sk_A)
% 2.74/2.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ X1))
% 2.74/2.99          | ~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ X1))),
% 2.74/2.99      inference('sup-', [status(thm)], ['136', '137'])).
% 2.74/2.99  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 2.74/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.99  thf('140', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ X1))
% 2.74/2.99          | ~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ X1))),
% 2.74/2.99      inference('demod', [status(thm)], ['138', '139'])).
% 2.74/2.99  thf('141', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         (~ (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['135', '140'])).
% 2.74/2.99  thf('142', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['99', '100'])).
% 2.74/2.99  thf('143', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)))
% 2.74/2.99         <= ((![X37 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99                 | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99                 | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))))),
% 2.74/2.99      inference('split', [status(esa)], ['19'])).
% 2.74/2.99  thf('144', plain,
% 2.74/2.99      ((![X0 : $i]:
% 2.74/2.99          ((r1_tarski @ sk_B @ X0)
% 2.74/2.99           | (r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 2.74/2.99           | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)))
% 2.74/2.99         <= ((![X37 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99                 | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99                 | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['142', '143'])).
% 2.74/2.99  thf('145', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('146', plain,
% 2.74/2.99      ((![X0 : $i]:
% 2.74/2.99          ((r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 2.74/2.99           | (r1_tarski @ sk_B @ X0)))
% 2.74/2.99         <= ((![X37 : $i]:
% 2.74/2.99                (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99                 | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99                 | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))))),
% 2.74/2.99      inference('clc', [status(thm)], ['144', '145'])).
% 2.74/2.99  thf('147', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B))) | 
% 2.74/2.99       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.74/2.99      inference('split', [status(esa)], ['19'])).
% 2.74/2.99  thf('148', plain,
% 2.74/2.99      ((![X37 : $i]:
% 2.74/2.99          (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ sk_A))
% 2.74/2.99           | ~ (r2_hidden @ X37 @ sk_B)
% 2.74/2.99           | (r1_tarski @ (sk_D_1 @ X37) @ sk_B)))),
% 2.74/2.99      inference('sat_resolution*', [status(thm)], ['2', '4', '55', '147'])).
% 2.74/2.99  thf('149', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ (sk_D_1 @ (sk_C @ X0 @ sk_B)) @ sk_B)
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('simpl_trail', [status(thm)], ['146', '148'])).
% 2.74/2.99  thf('150', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r1_tarski @ (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B))) @ 
% 2.74/2.99             (k1_tops_1 @ sk_A @ sk_B)))),
% 2.74/2.99      inference('clc', [status(thm)], ['141', '149'])).
% 2.74/2.99  thf('151', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.99         (~ (r2_hidden @ X0 @ X1)
% 2.74/2.99          | (r2_hidden @ X0 @ X2)
% 2.74/2.99          | ~ (r1_tarski @ X1 @ X2))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('152', plain,
% 2.74/2.99      (![X0 : $i, X1 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | ~ (r2_hidden @ X1 @ 
% 2.74/2.99               (k1_tops_1 @ sk_A @ (sk_D_1 @ (sk_C @ X0 @ sk_B)))))),
% 2.74/2.99      inference('sup-', [status(thm)], ['150', '151'])).
% 2.74/2.99  thf('153', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r1_tarski @ sk_B @ X0)
% 2.74/2.99          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('sup-', [status(thm)], ['134', '152'])).
% 2.74/2.99  thf('154', plain,
% 2.74/2.99      (![X0 : $i]:
% 2.74/2.99         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99          | (r1_tarski @ sk_B @ X0))),
% 2.74/2.99      inference('simplify', [status(thm)], ['153'])).
% 2.74/2.99  thf('155', plain,
% 2.74/2.99      (![X1 : $i, X3 : $i]:
% 2.74/2.99         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.74/2.99      inference('cnf', [status(esa)], [d3_tarski])).
% 2.74/2.99  thf('156', plain,
% 2.74/2.99      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.74/2.99        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.74/2.99      inference('sup-', [status(thm)], ['154', '155'])).
% 2.74/2.99  thf('157', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 2.74/2.99      inference('simplify', [status(thm)], ['156'])).
% 2.74/2.99  thf('158', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 2.74/2.99      inference('demod', [status(thm)], ['96', '157'])).
% 2.74/2.99  thf('159', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 2.74/2.99      inference('demod', [status(thm)], ['63', '158'])).
% 2.74/2.99  thf('160', plain, ($false), inference('demod', [status(thm)], ['57', '159'])).
% 2.74/2.99  
% 2.74/2.99  % SZS output end Refutation
% 2.74/2.99  
% 2.74/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
