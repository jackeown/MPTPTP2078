%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDaWIFzUcB

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:57 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 765 expanded)
%              Number of leaves         :   25 ( 205 expanded)
%              Depth                    :   34
%              Number of atoms          : 2146 (15354 expanded)
%              Number of equality atoms :   25 ( 116 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X30 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('9',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('13',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( v3_pre_topc @ X20 @ X19 )
        | ( ( k1_tops_1 @ X19 @ X20 )
          = X20 ) )
    | ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 ) ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X20 )
        = X20 ) ) ),
    inference(simpl_trail,[status(thm)],['13','21'])).

thf('23',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C_1 )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','42'])).

thf('44',plain,
    ( ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X30 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X30 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','44'])).

thf('46',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('49',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ~ ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
        | ~ ( l1_pre_topc @ X22 )
        | ~ ( v2_pre_topc @ X22 )
        | ( ( k1_tops_1 @ X22 @ X21 )
         != X21 )
        | ( v3_pre_topc @ X21 @ X22 ) )
    | ! [X19: $i,X20: $i] :
        ( ~ ( l1_pre_topc @ X19 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(split,[status(esa)],['48'])).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != X21 )
      | ( v3_pre_topc @ X21 @ X22 ) ) ),
    inference(simpl_trail,[status(thm)],['49','56'])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

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

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('79',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['79'])).

thf('82',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','44','81'])).

thf('83',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_1 @ X29 ) @ sk_A @ X29 ) ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['84','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('92',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('95',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','44','94'])).

thf('96',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_connsp_2 @ X25 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('112',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('113',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X29 @ sk_B )
        | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('114',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','44','113'])).

thf('115',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ( r1_tarski @ ( sk_D_1 @ X29 ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['112','114'])).

thf('116',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('118',plain,
    ( ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('120',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','129'])).

thf('131',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('133',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','138'])).

thf('140',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['61','139'])).

thf('141',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['46','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDaWIFzUcB
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:23:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.75/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/1.01  % Solved by: fo/fo7.sh
% 0.75/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/1.01  % done 757 iterations in 0.538s
% 0.75/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/1.01  % SZS output start Refutation
% 0.75/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/1.01  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/1.01  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.75/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.75/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/1.01  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.75/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.75/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/1.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.75/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/1.01  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.75/1.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/1.01  thf(t9_connsp_2, conjecture,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01           ( ( v3_pre_topc @ B @ A ) <=>
% 0.75/1.01             ( ![C:$i]:
% 0.75/1.01               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.75/1.01                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.75/1.01                      ( ![D:$i]:
% 0.75/1.01                        ( ( m1_subset_1 @
% 0.75/1.01                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.75/1.01                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.75/1.01    (~( ![A:$i]:
% 0.75/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/1.01            ( l1_pre_topc @ A ) ) =>
% 0.75/1.01          ( ![B:$i]:
% 0.75/1.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01              ( ( v3_pre_topc @ B @ A ) <=>
% 0.75/1.01                ( ![C:$i]:
% 0.75/1.01                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.75/1.01                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.75/1.01                         ( ![D:$i]:
% 0.75/1.01                           ( ( m1_subset_1 @
% 0.75/1.01                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.75/1.01                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/1.01    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 0.75/1.01  thf('0', plain,
% 0.75/1.01      (![X30 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01          | ~ (r1_tarski @ X30 @ sk_B)
% 0.75/1.01          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('1', plain,
% 0.75/1.01      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.75/1.01      inference('split', [status(esa)], ['0'])).
% 0.75/1.01  thf('2', plain,
% 0.75/1.01      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.75/1.01       (![X30 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01           | ~ (r1_tarski @ X30 @ sk_B)))),
% 0.75/1.01      inference('split', [status(esa)], ['0'])).
% 0.75/1.01  thf('3', plain,
% 0.75/1.01      (((r2_hidden @ sk_C_1 @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('4', plain,
% 0.75/1.01      (((r2_hidden @ sk_C_1 @ sk_B)) | ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('split', [status(esa)], ['3'])).
% 0.75/1.01  thf('5', plain,
% 0.75/1.01      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.75/1.01        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('6', plain,
% 0.75/1.01      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))) | 
% 0.75/1.01       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('split', [status(esa)], ['5'])).
% 0.75/1.01  thf('7', plain,
% 0.75/1.01      (((r2_hidden @ sk_C_1 @ sk_B)) <= (((r2_hidden @ sk_C_1 @ sk_B)))),
% 0.75/1.01      inference('split', [status(esa)], ['3'])).
% 0.75/1.01  thf('8', plain,
% 0.75/1.01      (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01         <= (((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('split', [status(esa)], ['5'])).
% 0.75/1.01  thf('9', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (r1_tarski @ (sk_D_1 @ X29) @ sk_B)
% 0.75/1.01          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('10', plain,
% 0.75/1.01      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.75/1.01      inference('split', [status(esa)], ['9'])).
% 0.75/1.01  thf('11', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(t55_tops_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( l1_pre_topc @ B ) =>
% 0.75/1.01           ( ![C:$i]:
% 0.75/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01               ( ![D:$i]:
% 0.75/1.01                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.75/1.01                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.75/1.01                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.75/1.01                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.75/1.01                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.75/1.01  thf('12', plain,
% 0.75/1.01      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.75/1.01         (~ (l1_pre_topc @ X19)
% 0.75/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01          | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01          | ((k1_tops_1 @ X19 @ X20) = (X20))
% 0.75/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01          | ~ (l1_pre_topc @ X22)
% 0.75/1.01          | ~ (v2_pre_topc @ X22))),
% 0.75/1.01      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.75/1.01  thf('13', plain,
% 0.75/1.01      ((![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01           | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01           | ((k1_tops_1 @ X19 @ X20) = (X20))))
% 0.75/1.01         <= ((![X19 : $i, X20 : $i]:
% 0.75/1.01                (~ (l1_pre_topc @ X19)
% 0.75/1.01                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01                 | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01                 | ((k1_tops_1 @ X19 @ X20) = (X20)))))),
% 0.75/1.01      inference('split', [status(esa)], ['12'])).
% 0.75/1.01  thf('14', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('15', plain,
% 0.75/1.01      ((![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)))
% 0.75/1.01         <= ((![X21 : $i, X22 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01                 | ~ (l1_pre_topc @ X22)
% 0.75/1.01                 | ~ (v2_pre_topc @ X22))))),
% 0.75/1.01      inference('split', [status(esa)], ['12'])).
% 0.75/1.01  thf('16', plain,
% 0.75/1.01      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.75/1.01         <= ((![X21 : $i, X22 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01                 | ~ (l1_pre_topc @ X22)
% 0.75/1.01                 | ~ (v2_pre_topc @ X22))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/1.01  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('19', plain,
% 0.75/1.01      (~
% 0.75/1.01       (![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)))),
% 0.75/1.01      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.75/1.01  thf('20', plain,
% 0.75/1.01      ((![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01           | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01           | ((k1_tops_1 @ X19 @ X20) = (X20)))) | 
% 0.75/1.01       (![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)))),
% 0.75/1.01      inference('split', [status(esa)], ['12'])).
% 0.75/1.01  thf('21', plain,
% 0.75/1.01      ((![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01           | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01           | ((k1_tops_1 @ X19 @ X20) = (X20))))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.75/1.01  thf('22', plain,
% 0.75/1.01      (![X19 : $i, X20 : $i]:
% 0.75/1.01         (~ (l1_pre_topc @ X19)
% 0.75/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01          | ~ (v3_pre_topc @ X20 @ X19)
% 0.75/1.01          | ((k1_tops_1 @ X19 @ X20) = (X20)))),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['13', '21'])).
% 0.75/1.01  thf('23', plain,
% 0.75/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.75/1.01        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.75/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.75/1.01      inference('sup-', [status(thm)], ['11', '22'])).
% 0.75/1.01  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('25', plain,
% 0.75/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/1.01  thf('26', plain,
% 0.75/1.01      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.75/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['10', '25'])).
% 0.75/1.01  thf('27', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(d1_connsp_2, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/1.01           ( ![C:$i]:
% 0.75/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.75/1.01                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.75/1.01  thf('28', plain,
% 0.75/1.01      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.75/1.01          | ~ (r2_hidden @ X23 @ (k1_tops_1 @ X24 @ X25))
% 0.75/1.01          | (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.75/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.75/1.01          | ~ (l1_pre_topc @ X24)
% 0.75/1.01          | ~ (v2_pre_topc @ X24)
% 0.75/1.01          | (v2_struct_0 @ X24))),
% 0.75/1.01      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.75/1.01  thf('29', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((v2_struct_0 @ sk_A)
% 0.75/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.75/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.75/1.01          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.75/1.01          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/1.01  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('32', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((v2_struct_0 @ sk_A)
% 0.75/1.01          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.75/1.01          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.75/1.01  thf('33', plain,
% 0.75/1.01      ((![X0 : $i]:
% 0.75/1.01          (~ (r2_hidden @ X0 @ sk_B)
% 0.75/1.01           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.75/1.01           | (v2_struct_0 @ sk_A)))
% 0.75/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['26', '32'])).
% 0.75/1.01  thf('34', plain,
% 0.75/1.01      ((((v2_struct_0 @ sk_A)
% 0.75/1.01         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)
% 0.75/1.01         | ~ (r2_hidden @ sk_C_1 @ sk_B)))
% 0.75/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 0.75/1.01             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['8', '33'])).
% 0.75/1.01  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('36', plain,
% 0.75/1.01      (((~ (r2_hidden @ sk_C_1 @ sk_B) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 0.75/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 0.75/1.01             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('clc', [status(thm)], ['34', '35'])).
% 0.75/1.01  thf('37', plain,
% 0.75/1.01      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 0.75/1.01         <= (((v3_pre_topc @ sk_B @ sk_A)) & 
% 0.75/1.01             ((r2_hidden @ sk_C_1 @ sk_B)) & 
% 0.75/1.01             ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['7', '36'])).
% 0.75/1.01  thf('38', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('39', plain,
% 0.75/1.01      ((![X30 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01           | ~ (r1_tarski @ X30 @ sk_B)))
% 0.75/1.01         <= ((![X30 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 0.75/1.01      inference('split', [status(esa)], ['0'])).
% 0.75/1.01  thf('40', plain,
% 0.75/1.01      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1)))
% 0.75/1.01         <= ((![X30 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/1.01  thf(d10_xboole_0, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/1.01  thf('41', plain,
% 0.75/1.01      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.75/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.01  thf('42', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.75/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.75/1.01  thf('43', plain,
% 0.75/1.01      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C_1))
% 0.75/1.01         <= ((![X30 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01                 | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 0.75/1.01      inference('demod', [status(thm)], ['40', '42'])).
% 0.75/1.01  thf('44', plain,
% 0.75/1.01      (~
% 0.75/1.01       (![X30 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01           | ~ (m1_connsp_2 @ X30 @ sk_A @ sk_C_1)
% 0.75/1.01           | ~ (r1_tarski @ X30 @ sk_B))) | 
% 0.75/1.01       ~ ((v3_pre_topc @ sk_B @ sk_A)) | ~ ((r2_hidden @ sk_C_1 @ sk_B)) | 
% 0.75/1.01       ~ ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['37', '43'])).
% 0.75/1.01  thf('45', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '44'])).
% 0.75/1.01  thf('46', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['1', '45'])).
% 0.75/1.01  thf('47', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('48', plain,
% 0.75/1.01      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.75/1.01         (~ (l1_pre_topc @ X19)
% 0.75/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.75/1.01          | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01          | (v3_pre_topc @ X21 @ X22)
% 0.75/1.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01          | ~ (l1_pre_topc @ X22)
% 0.75/1.01          | ~ (v2_pre_topc @ X22))),
% 0.75/1.01      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.75/1.01  thf('49', plain,
% 0.75/1.01      ((![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)
% 0.75/1.01           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01           | (v3_pre_topc @ X21 @ X22)))
% 0.75/1.01         <= ((![X21 : $i, X22 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01                 | ~ (l1_pre_topc @ X22)
% 0.75/1.01                 | ~ (v2_pre_topc @ X22)
% 0.75/1.01                 | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01                 | (v3_pre_topc @ X21 @ X22))))),
% 0.75/1.01      inference('split', [status(esa)], ['48'])).
% 0.75/1.01  thf('50', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('51', plain,
% 0.75/1.01      ((![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))
% 0.75/1.01         <= ((![X19 : $i, X20 : $i]:
% 0.75/1.01                (~ (l1_pre_topc @ X19)
% 0.75/1.01                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))))),
% 0.75/1.01      inference('split', [status(esa)], ['48'])).
% 0.75/1.01  thf('52', plain,
% 0.75/1.01      ((~ (l1_pre_topc @ sk_A))
% 0.75/1.01         <= ((![X19 : $i, X20 : $i]:
% 0.75/1.01                (~ (l1_pre_topc @ X19)
% 0.75/1.01                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/1.01  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('54', plain,
% 0.75/1.01      (~
% 0.75/1.01       (![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.75/1.01      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/1.01  thf('55', plain,
% 0.75/1.01      ((![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)
% 0.75/1.01           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01           | (v3_pre_topc @ X21 @ X22))) | 
% 0.75/1.01       (![X19 : $i, X20 : $i]:
% 0.75/1.01          (~ (l1_pre_topc @ X19)
% 0.75/1.01           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.75/1.01      inference('split', [status(esa)], ['48'])).
% 0.75/1.01  thf('56', plain,
% 0.75/1.01      ((![X21 : $i, X22 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01           | ~ (l1_pre_topc @ X22)
% 0.75/1.01           | ~ (v2_pre_topc @ X22)
% 0.75/1.01           | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01           | (v3_pre_topc @ X21 @ X22)))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.75/1.01  thf('57', plain,
% 0.75/1.01      (![X21 : $i, X22 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.75/1.01          | ~ (l1_pre_topc @ X22)
% 0.75/1.01          | ~ (v2_pre_topc @ X22)
% 0.75/1.01          | ((k1_tops_1 @ X22 @ X21) != (X21))
% 0.75/1.01          | (v3_pre_topc @ X21 @ X22))),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['49', '56'])).
% 0.75/1.01  thf('58', plain,
% 0.75/1.01      (((v3_pre_topc @ sk_B @ sk_A)
% 0.75/1.01        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 0.75/1.01        | ~ (v2_pre_topc @ sk_A)
% 0.75/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.75/1.01      inference('sup-', [status(thm)], ['47', '57'])).
% 0.75/1.01  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('61', plain,
% 0.75/1.01      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.75/1.01  thf('62', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(t44_tops_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( l1_pre_topc @ A ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.75/1.01  thf('63', plain,
% 0.75/1.01      (![X14 : $i, X15 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.75/1.01          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.75/1.01          | ~ (l1_pre_topc @ X15))),
% 0.75/1.01      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.75/1.01  thf('64', plain,
% 0.75/1.01      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/1.01  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('66', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.75/1.01      inference('demod', [status(thm)], ['64', '65'])).
% 0.75/1.01  thf('67', plain,
% 0.75/1.01      (![X4 : $i, X6 : $i]:
% 0.75/1.01         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.75/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/1.01  thf('68', plain,
% 0.75/1.01      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/1.01  thf('69', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('70', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf(dt_k1_tops_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( ( l1_pre_topc @ A ) & 
% 0.75/1.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.75/1.01       ( m1_subset_1 @
% 0.75/1.01         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.75/1.01  thf('71', plain,
% 0.75/1.01      (![X10 : $i, X11 : $i]:
% 0.75/1.01         (~ (l1_pre_topc @ X10)
% 0.75/1.01          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.75/1.01          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.75/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.75/1.01      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.75/1.01  thf('72', plain,
% 0.75/1.01      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.75/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | ~ (l1_pre_topc @ sk_A))),
% 0.75/1.01      inference('sup-', [status(thm)], ['70', '71'])).
% 0.75/1.01  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('74', plain,
% 0.75/1.01      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.75/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.01  thf(t7_subset_1, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/1.01       ( ![C:$i]:
% 0.75/1.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/1.01           ( ( ![D:$i]:
% 0.75/1.01               ( ( m1_subset_1 @ D @ A ) =>
% 0.75/1.01                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.75/1.01             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.75/1.01  thf('75', plain,
% 0.75/1.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.75/1.01          | (r1_tarski @ X9 @ X7)
% 0.75/1.01          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 0.75/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.75/1.01      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.75/1.01  thf('76', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | (m1_subset_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             (u1_struct_0 @ sk_A))
% 0.75/1.01          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['74', '75'])).
% 0.75/1.01  thf('77', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_subset_1 @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['69', '76'])).
% 0.75/1.01  thf('78', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_subset_1 @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['69', '76'])).
% 0.75/1.01  thf('79', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29)
% 0.75/1.01          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('80', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29)))
% 0.75/1.01         <= ((![X29 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01                 | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01                 | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29))))),
% 0.75/1.01      inference('split', [status(esa)], ['79'])).
% 0.75/1.01  thf('81', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29))) | 
% 0.75/1.01       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('split', [status(esa)], ['79'])).
% 0.75/1.01  thf('82', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29)))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '44', '81'])).
% 0.75/1.01  thf('83', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (m1_connsp_2 @ (sk_D_1 @ X29) @ sk_A @ X29))),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.75/1.01  thf('84', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_connsp_2 @ 
% 0.75/1.01           (sk_D_1 @ 
% 0.75/1.01            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01           sk_A @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | ~ (r2_hidden @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['78', '83'])).
% 0.75/1.01  thf('85', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('86', plain,
% 0.75/1.01      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.75/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.01  thf('87', plain,
% 0.75/1.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.75/1.01          | (r1_tarski @ X9 @ X7)
% 0.75/1.01          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.75/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.75/1.01      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.75/1.01  thf('88', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | (r2_hidden @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             X0)
% 0.75/1.01          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/1.01  thf('89', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['85', '88'])).
% 0.75/1.01  thf('90', plain,
% 0.75/1.01      (((m1_connsp_2 @ 
% 0.75/1.01         (sk_D_1 @ 
% 0.75/1.01          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01         sk_A @ 
% 0.75/1.01         (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('clc', [status(thm)], ['84', '89'])).
% 0.75/1.01  thf('91', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_subset_1 @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['69', '76'])).
% 0.75/1.01  thf('92', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | (v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('93', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01         <= ((![X29 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01                 | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01                 | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 0.75/1.01      inference('split', [status(esa)], ['92'])).
% 0.75/1.01  thf('94', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 0.75/1.01       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('split', [status(esa)], ['92'])).
% 0.75/1.01  thf('95', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '44', '94'])).
% 0.75/1.01  thf('96', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (m1_subset_1 @ (sk_D_1 @ X29) @ 
% 0.75/1.01             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 0.75/1.01  thf('97', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_subset_1 @ 
% 0.75/1.01           (sk_D_1 @ 
% 0.75/1.01            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | ~ (r2_hidden @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['91', '96'])).
% 0.75/1.01  thf('98', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['85', '88'])).
% 0.75/1.01  thf('99', plain,
% 0.75/1.01      (((m1_subset_1 @ 
% 0.75/1.01         (sk_D_1 @ 
% 0.75/1.01          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('clc', [status(thm)], ['97', '98'])).
% 0.75/1.01  thf('100', plain,
% 0.75/1.01      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.75/1.01          | ~ (m1_connsp_2 @ X25 @ X24 @ X23)
% 0.75/1.01          | (r2_hidden @ X23 @ (k1_tops_1 @ X24 @ X25))
% 0.75/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.75/1.01          | ~ (l1_pre_topc @ X24)
% 0.75/1.01          | ~ (v2_pre_topc @ X24)
% 0.75/1.01          | (v2_struct_0 @ X24))),
% 0.75/1.01      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.75/1.01  thf('101', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | (v2_struct_0 @ sk_A)
% 0.75/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.75/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.75/1.01          | (r2_hidden @ X0 @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ 
% 0.75/1.01              (sk_D_1 @ 
% 0.75/1.01               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01          | ~ (m1_connsp_2 @ 
% 0.75/1.01               (sk_D_1 @ 
% 0.75/1.01                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01               sk_A @ X0)
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['99', '100'])).
% 0.75/1.01  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('104', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | (v2_struct_0 @ sk_A)
% 0.75/1.01          | (r2_hidden @ X0 @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ 
% 0.75/1.01              (sk_D_1 @ 
% 0.75/1.01               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01          | ~ (m1_connsp_2 @ 
% 0.75/1.01               (sk_D_1 @ 
% 0.75/1.01                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01               sk_A @ X0)
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.75/1.01  thf('105', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | ~ (m1_subset_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             (u1_struct_0 @ sk_A))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01        | (v2_struct_0 @ sk_A)
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['90', '104'])).
% 0.75/1.01  thf('106', plain,
% 0.75/1.01      (((v2_struct_0 @ sk_A)
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01        | ~ (m1_subset_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             (u1_struct_0 @ sk_A))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('simplify', [status(thm)], ['105'])).
% 0.75/1.01  thf('107', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01        | (v2_struct_0 @ sk_A))),
% 0.75/1.01      inference('sup-', [status(thm)], ['77', '106'])).
% 0.75/1.01  thf('108', plain,
% 0.75/1.01      (((v2_struct_0 @ sk_A)
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('simplify', [status(thm)], ['107'])).
% 0.75/1.01  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('110', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.75/1.01      inference('clc', [status(thm)], ['108', '109'])).
% 0.75/1.01  thf('111', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (m1_subset_1 @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['69', '76'])).
% 0.75/1.01  thf('112', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (r1_tarski @ (sk_D_1 @ X29) @ sk_B)))
% 0.75/1.01         <= ((![X29 : $i]:
% 0.75/1.01                (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01                 | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01                 | (r1_tarski @ (sk_D_1 @ X29) @ sk_B))))),
% 0.75/1.01      inference('split', [status(esa)], ['9'])).
% 0.75/1.01  thf('113', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (r1_tarski @ (sk_D_1 @ X29) @ sk_B))) | 
% 0.75/1.01       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.75/1.01      inference('split', [status(esa)], ['9'])).
% 0.75/1.01  thf('114', plain,
% 0.75/1.01      ((![X29 : $i]:
% 0.75/1.01          (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01           | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01           | (r1_tarski @ (sk_D_1 @ X29) @ sk_B)))),
% 0.75/1.01      inference('sat_resolution*', [status(thm)], ['2', '4', '6', '44', '113'])).
% 0.75/1.01  thf('115', plain,
% 0.75/1.01      (![X29 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A))
% 0.75/1.01          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/1.01          | (r1_tarski @ (sk_D_1 @ X29) @ sk_B))),
% 0.75/1.01      inference('simpl_trail', [status(thm)], ['112', '114'])).
% 0.75/1.01  thf('116', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ 
% 0.75/1.01           (sk_D_1 @ 
% 0.75/1.01            (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01           sk_B)
% 0.75/1.01        | ~ (r2_hidden @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01             sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['111', '115'])).
% 0.75/1.01  thf('117', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           sk_B))),
% 0.75/1.01      inference('sup-', [status(thm)], ['85', '88'])).
% 0.75/1.01  thf('118', plain,
% 0.75/1.01      (((r1_tarski @ 
% 0.75/1.01         (sk_D_1 @ 
% 0.75/1.01          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01         sk_B)
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('clc', [status(thm)], ['116', '117'])).
% 0.75/1.01  thf('119', plain,
% 0.75/1.01      (((m1_subset_1 @ 
% 0.75/1.01         (sk_D_1 @ 
% 0.75/1.01          (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('clc', [status(thm)], ['97', '98'])).
% 0.75/1.01  thf(t48_tops_1, axiom,
% 0.75/1.01    (![A:$i]:
% 0.75/1.01     ( ( l1_pre_topc @ A ) =>
% 0.75/1.01       ( ![B:$i]:
% 0.75/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01           ( ![C:$i]:
% 0.75/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.75/1.01               ( ( r1_tarski @ B @ C ) =>
% 0.75/1.01                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.75/1.01  thf('120', plain,
% 0.75/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/1.01          | ~ (r1_tarski @ X16 @ X18)
% 0.75/1.01          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ (k1_tops_1 @ X17 @ X18))
% 0.75/1.01          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.75/1.01          | ~ (l1_pre_topc @ X17))),
% 0.75/1.01      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.75/1.01  thf('121', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | (r1_tarski @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ 
% 0.75/1.01              (sk_D_1 @ 
% 0.75/1.01               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ X0))
% 0.75/1.01          | ~ (r1_tarski @ 
% 0.75/1.01               (sk_D_1 @ 
% 0.75/1.01                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01               X0))),
% 0.75/1.01      inference('sup-', [status(thm)], ['119', '120'])).
% 0.75/1.01  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('123', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | (r1_tarski @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ 
% 0.75/1.01              (sk_D_1 @ 
% 0.75/1.01               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.75/1.01             (k1_tops_1 @ sk_A @ X0))
% 0.75/1.01          | ~ (r1_tarski @ 
% 0.75/1.01               (sk_D_1 @ 
% 0.75/1.01                (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.75/1.01               X0))),
% 0.75/1.01      inference('demod', [status(thm)], ['121', '122'])).
% 0.75/1.01  thf('124', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['118', '123'])).
% 0.75/1.01  thf('125', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('126', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ 
% 0.75/1.01            (sk_D_1 @ 
% 0.75/1.01             (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['124', '125'])).
% 0.75/1.01  thf('127', plain,
% 0.75/1.01      (((r1_tarski @ 
% 0.75/1.01         (k1_tops_1 @ sk_A @ 
% 0.75/1.01          (sk_D_1 @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.75/1.01         (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('simplify', [status(thm)], ['126'])).
% 0.75/1.01  thf(d3_tarski, axiom,
% 0.75/1.01    (![A:$i,B:$i]:
% 0.75/1.01     ( ( r1_tarski @ A @ B ) <=>
% 0.75/1.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/1.01  thf('128', plain,
% 0.75/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.01         (~ (r2_hidden @ X0 @ X1)
% 0.75/1.01          | (r2_hidden @ X0 @ X2)
% 0.75/1.01          | ~ (r1_tarski @ X1 @ X2))),
% 0.75/1.01      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/1.01  thf('129', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | ~ (r2_hidden @ X0 @ 
% 0.75/1.01               (k1_tops_1 @ sk_A @ 
% 0.75/1.01                (sk_D_1 @ 
% 0.75/1.01                 (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ 
% 0.75/1.01                  (u1_struct_0 @ sk_A))))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['127', '128'])).
% 0.75/1.01  thf('130', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r2_hidden @ 
% 0.75/1.01           (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01           (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['110', '129'])).
% 0.75/1.01  thf('131', plain,
% 0.75/1.01      (((r2_hidden @ 
% 0.75/1.01         (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01         (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('simplify', [status(thm)], ['130'])).
% 0.75/1.01  thf('132', plain,
% 0.75/1.01      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.75/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/1.01  thf('133', plain,
% 0.75/1.01      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.75/1.01          | (r1_tarski @ X9 @ X7)
% 0.75/1.01          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.75/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.75/1.01      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.75/1.01  thf('134', plain,
% 0.75/1.01      (![X0 : $i]:
% 0.75/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.75/1.01          | ~ (r2_hidden @ 
% 0.75/1.01               (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.75/1.01               (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('sup-', [status(thm)], ['132', '133'])).
% 0.75/1.01  thf('135', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.75/1.01      inference('sup-', [status(thm)], ['131', '134'])).
% 0.75/1.01  thf('136', plain,
% 0.75/1.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.75/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.01  thf('137', plain,
% 0.75/1.01      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.75/1.01        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['135', '136'])).
% 0.75/1.01  thf('138', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.75/1.01      inference('simplify', [status(thm)], ['137'])).
% 0.75/1.01  thf('139', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.75/1.01      inference('demod', [status(thm)], ['68', '138'])).
% 0.75/1.01  thf('140', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.75/1.01      inference('demod', [status(thm)], ['61', '139'])).
% 0.75/1.01  thf('141', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.75/1.01      inference('simplify', [status(thm)], ['140'])).
% 0.75/1.01  thf('142', plain, ($false), inference('demod', [status(thm)], ['46', '141'])).
% 0.75/1.01  
% 0.75/1.01  % SZS output end Refutation
% 0.75/1.01  
% 0.75/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
