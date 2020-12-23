%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vZnWNU1lMx

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:58 EST 2020

% Result     : Theorem 5.43s
% Output     : Refutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 782 expanded)
%              Number of leaves         :   26 ( 213 expanded)
%              Depth                    :   34
%              Number of atoms          : 2040 (14389 expanded)
%              Number of equality atoms :   25 ( 128 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
      | ~ ( r1_tarski @ X35 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X35 @ sk_B ) )
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

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ~ ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( v3_pre_topc @ X25 @ X24 )
        | ( ( k1_tops_1 @ X24 @ X25 )
          = X25 ) )
    | ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X25 )
        = X25 ) ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
      | ~ ( r2_hidden @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
        | ~ ( r1_tarski @ X35 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X35 @ sk_A @ sk_C )
          | ~ ( r1_tarski @ X35 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46'])).

thf('48',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('51',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
    | ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference(simpl_trail,[status(thm)],['51','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('72',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('75',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

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

thf('77',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ sk_B ) @ X0 )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('83',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('86',plain,
    ( ! [X34: $i] :
        ( ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 )
        | ~ ( r2_hidden @ X34 @ sk_B ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','88'])).

thf('90',plain,(
    ! [X34: $i] :
      ( ( m1_connsp_2 @ ( sk_D_2 @ X34 ) @ sk_A @ X34 )
      | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['86','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('93',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('96',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','95'])).

thf('97',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('99',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( sk_D_2 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('113',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('114',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X34 @ sk_B )
        | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('115',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','46','114'])).

thf('116',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['113','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('118',plain,(
    ! [X34: $i] :
      ( ( r1_tarski @ ( sk_D_2 @ X34 ) @ sk_B )
      | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('131',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( sk_D_2 @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','132'])).

thf('134',plain,
    ( ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('136',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('140',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','141'])).

thf('143',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','142'])).

thf('144',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['48','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vZnWNU1lMx
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:26:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.43/5.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.43/5.61  % Solved by: fo/fo7.sh
% 5.43/5.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.43/5.61  % done 6089 iterations in 5.150s
% 5.43/5.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.43/5.61  % SZS output start Refutation
% 5.43/5.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.43/5.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.43/5.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.43/5.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.43/5.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.43/5.61  thf(sk_B_type, type, sk_B: $i).
% 5.43/5.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.43/5.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.43/5.61  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 5.43/5.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.43/5.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.43/5.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.43/5.61  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 5.43/5.61  thf(sk_C_type, type, sk_C: $i).
% 5.43/5.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.43/5.61  thf(sk_A_type, type, sk_A: $i).
% 5.43/5.61  thf(t9_connsp_2, conjecture,
% 5.43/5.61    (![A:$i]:
% 5.43/5.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.43/5.61       ( ![B:$i]:
% 5.43/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61           ( ( v3_pre_topc @ B @ A ) <=>
% 5.43/5.61             ( ![C:$i]:
% 5.43/5.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.43/5.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 5.43/5.61                      ( ![D:$i]:
% 5.43/5.61                        ( ( m1_subset_1 @
% 5.43/5.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 5.43/5.61                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 5.43/5.61  thf(zf_stmt_0, negated_conjecture,
% 5.43/5.61    (~( ![A:$i]:
% 5.43/5.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.43/5.61            ( l1_pre_topc @ A ) ) =>
% 5.43/5.61          ( ![B:$i]:
% 5.43/5.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61              ( ( v3_pre_topc @ B @ A ) <=>
% 5.43/5.61                ( ![C:$i]:
% 5.43/5.61                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.43/5.61                    ( ~( ( r2_hidden @ C @ B ) & 
% 5.43/5.61                         ( ![D:$i]:
% 5.43/5.61                           ( ( m1_subset_1 @
% 5.43/5.61                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61                             ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 5.43/5.61                                  ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 5.43/5.61    inference('cnf.neg', [status(esa)], [t9_connsp_2])).
% 5.43/5.61  thf('0', plain,
% 5.43/5.61      (![X35 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61          | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61          | ~ (r1_tarski @ X35 @ sk_B)
% 5.43/5.61          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('1', plain,
% 5.43/5.61      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 5.43/5.61      inference('split', [status(esa)], ['0'])).
% 5.43/5.61  thf('2', plain,
% 5.43/5.61      ((![X35 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61           | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61           | ~ (r1_tarski @ X35 @ sk_B))) | 
% 5.43/5.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('split', [status(esa)], ['0'])).
% 5.43/5.61  thf('3', plain,
% 5.43/5.61      (((r2_hidden @ sk_C @ sk_B) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('4', plain,
% 5.43/5.61      (~ ((v3_pre_topc @ sk_B @ sk_A)) | ((r2_hidden @ sk_C @ sk_B))),
% 5.43/5.61      inference('split', [status(esa)], ['3'])).
% 5.43/5.61  thf('5', plain,
% 5.43/5.61      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('split', [status(esa)], ['3'])).
% 5.43/5.61  thf('6', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf(t4_subset, axiom,
% 5.43/5.61    (![A:$i,B:$i,C:$i]:
% 5.43/5.61     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 5.43/5.61       ( m1_subset_1 @ A @ C ) ))).
% 5.43/5.61  thf('7', plain,
% 5.43/5.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.43/5.61         (~ (r2_hidden @ X12 @ X13)
% 5.43/5.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.43/5.61          | (m1_subset_1 @ X12 @ X14))),
% 5.43/5.61      inference('cnf', [status(esa)], [t4_subset])).
% 5.43/5.61  thf('8', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['6', '7'])).
% 5.43/5.61  thf('9', plain,
% 5.43/5.61      (((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 5.43/5.61         <= (((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['5', '8'])).
% 5.43/5.61  thf('10', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (r1_tarski @ (sk_D_2 @ X34) @ sk_B)
% 5.43/5.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('11', plain,
% 5.43/5.61      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.43/5.61      inference('split', [status(esa)], ['10'])).
% 5.43/5.61  thf('12', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf(t55_tops_1, axiom,
% 5.43/5.61    (![A:$i]:
% 5.43/5.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.43/5.61       ( ![B:$i]:
% 5.43/5.61         ( ( l1_pre_topc @ B ) =>
% 5.43/5.61           ( ![C:$i]:
% 5.43/5.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61               ( ![D:$i]:
% 5.43/5.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.43/5.61                   ( ( ( v3_pre_topc @ D @ B ) =>
% 5.43/5.61                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 5.43/5.61                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 5.43/5.61                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 5.43/5.61  thf('13', plain,
% 5.43/5.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.43/5.61         (~ (l1_pre_topc @ X24)
% 5.43/5.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61          | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61          | ((k1_tops_1 @ X24 @ X25) = (X25))
% 5.43/5.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61          | ~ (l1_pre_topc @ X27)
% 5.43/5.61          | ~ (v2_pre_topc @ X27))),
% 5.43/5.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 5.43/5.61  thf('14', plain,
% 5.43/5.61      ((![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61           | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61           | ((k1_tops_1 @ X24 @ X25) = (X25))))
% 5.43/5.61         <= ((![X24 : $i, X25 : $i]:
% 5.43/5.61                (~ (l1_pre_topc @ X24)
% 5.43/5.61                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61                 | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61                 | ((k1_tops_1 @ X24 @ X25) = (X25)))))),
% 5.43/5.61      inference('split', [status(esa)], ['13'])).
% 5.43/5.61  thf('15', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('16', plain,
% 5.43/5.61      ((![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)))
% 5.43/5.61         <= ((![X26 : $i, X27 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61                 | ~ (l1_pre_topc @ X27)
% 5.43/5.61                 | ~ (v2_pre_topc @ X27))))),
% 5.43/5.61      inference('split', [status(esa)], ['13'])).
% 5.43/5.61  thf('17', plain,
% 5.43/5.61      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 5.43/5.61         <= ((![X26 : $i, X27 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61                 | ~ (l1_pre_topc @ X27)
% 5.43/5.61                 | ~ (v2_pre_topc @ X27))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['15', '16'])).
% 5.43/5.61  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('20', plain,
% 5.43/5.61      (~
% 5.43/5.61       (![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)))),
% 5.43/5.61      inference('demod', [status(thm)], ['17', '18', '19'])).
% 5.43/5.61  thf('21', plain,
% 5.43/5.61      ((![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61           | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61           | ((k1_tops_1 @ X24 @ X25) = (X25)))) | 
% 5.43/5.61       (![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)))),
% 5.43/5.61      inference('split', [status(esa)], ['13'])).
% 5.43/5.61  thf('22', plain,
% 5.43/5.61      ((![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61           | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61           | ((k1_tops_1 @ X24 @ X25) = (X25))))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 5.43/5.61  thf('23', plain,
% 5.43/5.61      (![X24 : $i, X25 : $i]:
% 5.43/5.61         (~ (l1_pre_topc @ X24)
% 5.43/5.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61          | ~ (v3_pre_topc @ X25 @ X24)
% 5.43/5.61          | ((k1_tops_1 @ X24 @ X25) = (X25)))),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 5.43/5.61  thf('24', plain,
% 5.43/5.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 5.43/5.61        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 5.43/5.61        | ~ (l1_pre_topc @ sk_A))),
% 5.43/5.61      inference('sup-', [status(thm)], ['12', '23'])).
% 5.43/5.61  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('26', plain,
% 5.43/5.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('demod', [status(thm)], ['24', '25'])).
% 5.43/5.61  thf('27', plain,
% 5.43/5.61      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 5.43/5.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['11', '26'])).
% 5.43/5.61  thf('28', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf(d1_connsp_2, axiom,
% 5.43/5.61    (![A:$i]:
% 5.43/5.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.43/5.61       ( ![B:$i]:
% 5.43/5.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.43/5.61           ( ![C:$i]:
% 5.43/5.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 5.43/5.61                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.43/5.61  thf('29', plain,
% 5.43/5.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 5.43/5.61          | ~ (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 5.43/5.61          | (m1_connsp_2 @ X30 @ X29 @ X28)
% 5.43/5.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.43/5.61          | ~ (l1_pre_topc @ X29)
% 5.43/5.61          | ~ (v2_pre_topc @ X29)
% 5.43/5.61          | (v2_struct_0 @ X29))),
% 5.43/5.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 5.43/5.61  thf('30', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((v2_struct_0 @ sk_A)
% 5.43/5.61          | ~ (v2_pre_topc @ sk_A)
% 5.43/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.43/5.61          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 5.43/5.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['28', '29'])).
% 5.43/5.61  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('33', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((v2_struct_0 @ sk_A)
% 5.43/5.61          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 5.43/5.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 5.43/5.61  thf('34', plain,
% 5.43/5.61      ((![X0 : $i]:
% 5.43/5.61          (~ (r2_hidden @ X0 @ sk_B)
% 5.43/5.61           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 5.43/5.61           | (v2_struct_0 @ sk_A)))
% 5.43/5.61         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['27', '33'])).
% 5.43/5.61  thf('35', plain,
% 5.43/5.61      ((((v2_struct_0 @ sk_A)
% 5.43/5.61         | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)
% 5.43/5.61         | ~ (r2_hidden @ sk_C @ sk_B)))
% 5.43/5.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['9', '34'])).
% 5.43/5.61  thf('36', plain,
% 5.43/5.61      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('split', [status(esa)], ['3'])).
% 5.43/5.61  thf('37', plain,
% 5.43/5.61      ((((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)))
% 5.43/5.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('demod', [status(thm)], ['35', '36'])).
% 5.43/5.61  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('39', plain,
% 5.43/5.61      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C))
% 5.43/5.61         <= (((v3_pre_topc @ sk_B @ sk_A)) & ((r2_hidden @ sk_C @ sk_B)))),
% 5.43/5.61      inference('clc', [status(thm)], ['37', '38'])).
% 5.43/5.61  thf('40', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('41', plain,
% 5.43/5.61      ((![X35 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61           | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61           | ~ (r1_tarski @ X35 @ sk_B)))
% 5.43/5.61         <= ((![X35 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61                 | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61                 | ~ (r1_tarski @ X35 @ sk_B))))),
% 5.43/5.61      inference('split', [status(esa)], ['0'])).
% 5.43/5.61  thf('42', plain,
% 5.43/5.61      (((~ (r1_tarski @ sk_B @ sk_B) | ~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C)))
% 5.43/5.61         <= ((![X35 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61                 | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61                 | ~ (r1_tarski @ X35 @ sk_B))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['40', '41'])).
% 5.43/5.61  thf(d10_xboole_0, axiom,
% 5.43/5.61    (![A:$i,B:$i]:
% 5.43/5.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.43/5.61  thf('43', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.43/5.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.43/5.61  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.43/5.61      inference('simplify', [status(thm)], ['43'])).
% 5.43/5.61  thf('45', plain,
% 5.43/5.61      ((~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C))
% 5.43/5.61         <= ((![X35 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61                 | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61                 | ~ (r1_tarski @ X35 @ sk_B))))),
% 5.43/5.61      inference('demod', [status(thm)], ['42', '44'])).
% 5.43/5.61  thf('46', plain,
% 5.43/5.61      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 5.43/5.61       ~
% 5.43/5.61       (![X35 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61           | ~ (m1_connsp_2 @ X35 @ sk_A @ sk_C)
% 5.43/5.61           | ~ (r1_tarski @ X35 @ sk_B))) | 
% 5.43/5.61       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('sup-', [status(thm)], ['39', '45'])).
% 5.43/5.61  thf('47', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46'])).
% 5.43/5.61  thf('48', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 5.43/5.61  thf('49', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('50', plain,
% 5.43/5.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.43/5.61         (~ (l1_pre_topc @ X24)
% 5.43/5.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.43/5.61          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61          | (v3_pre_topc @ X26 @ X27)
% 5.43/5.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61          | ~ (l1_pre_topc @ X27)
% 5.43/5.61          | ~ (v2_pre_topc @ X27))),
% 5.43/5.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 5.43/5.61  thf('51', plain,
% 5.43/5.61      ((![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)
% 5.43/5.61           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61           | (v3_pre_topc @ X26 @ X27)))
% 5.43/5.61         <= ((![X26 : $i, X27 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61                 | ~ (l1_pre_topc @ X27)
% 5.43/5.61                 | ~ (v2_pre_topc @ X27)
% 5.43/5.61                 | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61                 | (v3_pre_topc @ X26 @ X27))))),
% 5.43/5.61      inference('split', [status(esa)], ['50'])).
% 5.43/5.61  thf('52', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('53', plain,
% 5.43/5.61      ((![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))
% 5.43/5.61         <= ((![X24 : $i, X25 : $i]:
% 5.43/5.61                (~ (l1_pre_topc @ X24)
% 5.43/5.61                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 5.43/5.61      inference('split', [status(esa)], ['50'])).
% 5.43/5.61  thf('54', plain,
% 5.43/5.61      ((~ (l1_pre_topc @ sk_A))
% 5.43/5.61         <= ((![X24 : $i, X25 : $i]:
% 5.43/5.61                (~ (l1_pre_topc @ X24)
% 5.43/5.61                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['52', '53'])).
% 5.43/5.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('56', plain,
% 5.43/5.61      (~
% 5.43/5.61       (![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 5.43/5.61      inference('demod', [status(thm)], ['54', '55'])).
% 5.43/5.61  thf('57', plain,
% 5.43/5.61      ((![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)
% 5.43/5.61           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61           | (v3_pre_topc @ X26 @ X27))) | 
% 5.43/5.61       (![X24 : $i, X25 : $i]:
% 5.43/5.61          (~ (l1_pre_topc @ X24)
% 5.43/5.61           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 5.43/5.61      inference('split', [status(esa)], ['50'])).
% 5.43/5.61  thf('58', plain,
% 5.43/5.61      ((![X26 : $i, X27 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61           | ~ (l1_pre_topc @ X27)
% 5.43/5.61           | ~ (v2_pre_topc @ X27)
% 5.43/5.61           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61           | (v3_pre_topc @ X26 @ X27)))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 5.43/5.61  thf('59', plain,
% 5.43/5.61      (![X26 : $i, X27 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 5.43/5.61          | ~ (l1_pre_topc @ X27)
% 5.43/5.61          | ~ (v2_pre_topc @ X27)
% 5.43/5.61          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 5.43/5.61          | (v3_pre_topc @ X26 @ X27))),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['51', '58'])).
% 5.43/5.61  thf('60', plain,
% 5.43/5.61      (((v3_pre_topc @ sk_B @ sk_A)
% 5.43/5.61        | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B))
% 5.43/5.61        | ~ (v2_pre_topc @ sk_A)
% 5.43/5.61        | ~ (l1_pre_topc @ sk_A))),
% 5.43/5.61      inference('sup-', [status(thm)], ['49', '59'])).
% 5.43/5.61  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('63', plain,
% 5.43/5.61      (((v3_pre_topc @ sk_B @ sk_A) | ((k1_tops_1 @ sk_A @ sk_B) != (sk_B)))),
% 5.43/5.61      inference('demod', [status(thm)], ['60', '61', '62'])).
% 5.43/5.61  thf('64', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf(t44_tops_1, axiom,
% 5.43/5.61    (![A:$i]:
% 5.43/5.61     ( ( l1_pre_topc @ A ) =>
% 5.43/5.61       ( ![B:$i]:
% 5.43/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 5.43/5.61  thf('65', plain,
% 5.43/5.61      (![X15 : $i, X16 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.43/5.61          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ X15)
% 5.43/5.61          | ~ (l1_pre_topc @ X16))),
% 5.43/5.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 5.43/5.61  thf('66', plain,
% 5.43/5.61      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['64', '65'])).
% 5.43/5.61  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('68', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.43/5.61      inference('demod', [status(thm)], ['66', '67'])).
% 5.43/5.61  thf('69', plain,
% 5.43/5.61      (![X0 : $i, X2 : $i]:
% 5.43/5.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.43/5.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.43/5.61  thf('70', plain,
% 5.43/5.61      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['68', '69'])).
% 5.43/5.61  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.43/5.61      inference('simplify', [status(thm)], ['43'])).
% 5.43/5.61  thf(t3_subset, axiom,
% 5.43/5.61    (![A:$i,B:$i]:
% 5.43/5.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.43/5.61  thf('72', plain,
% 5.43/5.61      (![X9 : $i, X11 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 5.43/5.61      inference('cnf', [status(esa)], [t3_subset])).
% 5.43/5.61  thf('73', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.43/5.61      inference('sup-', [status(thm)], ['71', '72'])).
% 5.43/5.61  thf('74', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.43/5.61      inference('demod', [status(thm)], ['66', '67'])).
% 5.43/5.61  thf('75', plain,
% 5.43/5.61      (![X9 : $i, X11 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 5.43/5.61      inference('cnf', [status(esa)], [t3_subset])).
% 5.43/5.61  thf('76', plain,
% 5.43/5.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['74', '75'])).
% 5.43/5.61  thf(t7_subset_1, axiom,
% 5.43/5.61    (![A:$i,B:$i]:
% 5.43/5.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.43/5.61       ( ![C:$i]:
% 5.43/5.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.43/5.61           ( ( ![D:$i]:
% 5.43/5.61               ( ( m1_subset_1 @ D @ A ) =>
% 5.43/5.61                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 5.43/5.61             ( r1_tarski @ B @ C ) ) ) ) ))).
% 5.43/5.61  thf('77', plain,
% 5.43/5.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 5.43/5.61          | (r1_tarski @ X8 @ X6)
% 5.43/5.61          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 5.43/5.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 5.43/5.61      inference('cnf', [status(esa)], [t7_subset_1])).
% 5.43/5.61  thf('78', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 5.43/5.61          | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ sk_B) @ X0)
% 5.43/5.61          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['76', '77'])).
% 5.43/5.61  thf('79', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['73', '78'])).
% 5.43/5.61  thf('80', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['6', '7'])).
% 5.43/5.61  thf('81', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['79', '80'])).
% 5.43/5.61  thf('82', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['73', '78'])).
% 5.43/5.61  thf('83', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)
% 5.43/5.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('84', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)))
% 5.43/5.61         <= ((![X34 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61                 | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61                 | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34))))),
% 5.43/5.61      inference('split', [status(esa)], ['83'])).
% 5.43/5.61  thf('85', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['6', '7'])).
% 5.43/5.61  thf('86', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          ((m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)))
% 5.43/5.61         <= ((![X34 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61                 | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61                 | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34))))),
% 5.43/5.61      inference('clc', [status(thm)], ['84', '85'])).
% 5.43/5.61  thf('87', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)
% 5.43/5.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('88', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34))) | 
% 5.43/5.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('split', [status(esa)], ['87'])).
% 5.43/5.61  thf('89', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '88'])).
% 5.43/5.61  thf('90', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         ((m1_connsp_2 @ (sk_D_2 @ X34) @ sk_A @ X34)
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B))),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['86', '89'])).
% 5.43/5.61  thf('91', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (m1_connsp_2 @ 
% 5.43/5.61           (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 5.43/5.61           sk_A @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['82', '90'])).
% 5.43/5.61  thf('92', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['73', '78'])).
% 5.43/5.61  thf('93', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61          | (v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('94', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 5.43/5.61         <= ((![X34 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61                 | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61                 | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61                    (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))),
% 5.43/5.61      inference('split', [status(esa)], ['93'])).
% 5.43/5.61  thf('95', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))) | 
% 5.43/5.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('split', [status(esa)], ['93'])).
% 5.43/5.61  thf('96', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '95'])).
% 5.43/5.61  thf('97', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (m1_subset_1 @ (sk_D_2 @ X34) @ 
% 5.43/5.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 5.43/5.61  thf('98', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['6', '7'])).
% 5.43/5.61  thf('99', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         ((m1_subset_1 @ (sk_D_2 @ X34) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B))),
% 5.43/5.61      inference('clc', [status(thm)], ['97', '98'])).
% 5.43/5.61  thf('100', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (m1_subset_1 @ 
% 5.43/5.61           (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 5.43/5.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['92', '99'])).
% 5.43/5.61  thf('101', plain,
% 5.43/5.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 5.43/5.61          | ~ (m1_connsp_2 @ X30 @ X29 @ X28)
% 5.43/5.61          | (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 5.43/5.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.43/5.61          | ~ (l1_pre_topc @ X29)
% 5.43/5.61          | ~ (v2_pre_topc @ X29)
% 5.43/5.61          | (v2_struct_0 @ X29))),
% 5.43/5.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 5.43/5.61  thf('102', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | (v2_struct_0 @ sk_A)
% 5.43/5.61          | ~ (v2_pre_topc @ sk_A)
% 5.43/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.43/5.61          | (r2_hidden @ X0 @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ 
% 5.43/5.61              (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61          | ~ (m1_connsp_2 @ 
% 5.43/5.61               (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 5.43/5.61               sk_A @ X0)
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['100', '101'])).
% 5.43/5.61  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('105', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | (v2_struct_0 @ sk_A)
% 5.43/5.61          | (r2_hidden @ X0 @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ 
% 5.43/5.61              (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61          | ~ (m1_connsp_2 @ 
% 5.43/5.61               (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 5.43/5.61               sk_A @ X0)
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('demod', [status(thm)], ['102', '103', '104'])).
% 5.43/5.61  thf('106', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | ~ (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61             (u1_struct_0 @ sk_A))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61        | (v2_struct_0 @ sk_A)
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['91', '105'])).
% 5.43/5.61  thf('107', plain,
% 5.43/5.61      (((v2_struct_0 @ sk_A)
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61        | ~ (m1_subset_1 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61             (u1_struct_0 @ sk_A))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('simplify', [status(thm)], ['106'])).
% 5.43/5.61  thf('108', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61        | (v2_struct_0 @ sk_A))),
% 5.43/5.61      inference('sup-', [status(thm)], ['81', '107'])).
% 5.43/5.61  thf('109', plain,
% 5.43/5.61      (((v2_struct_0 @ sk_A)
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('simplify', [status(thm)], ['108'])).
% 5.43/5.61  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('111', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))))),
% 5.43/5.61      inference('clc', [status(thm)], ['109', '110'])).
% 5.43/5.61  thf('112', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['73', '78'])).
% 5.43/5.61  thf('113', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (r1_tarski @ (sk_D_2 @ X34) @ sk_B)))
% 5.43/5.61         <= ((![X34 : $i]:
% 5.43/5.61                (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61                 | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61                 | (r1_tarski @ (sk_D_2 @ X34) @ sk_B))))),
% 5.43/5.61      inference('split', [status(esa)], ['10'])).
% 5.43/5.61  thf('114', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (r1_tarski @ (sk_D_2 @ X34) @ sk_B))) | 
% 5.43/5.61       ((v3_pre_topc @ sk_B @ sk_A))),
% 5.43/5.61      inference('split', [status(esa)], ['10'])).
% 5.43/5.61  thf('115', plain,
% 5.43/5.61      ((![X34 : $i]:
% 5.43/5.61          (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61           | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61           | (r1_tarski @ (sk_D_2 @ X34) @ sk_B)))),
% 5.43/5.61      inference('sat_resolution*', [status(thm)], ['2', '4', '46', '114'])).
% 5.43/5.61  thf('116', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_A))
% 5.43/5.61          | ~ (r2_hidden @ X34 @ sk_B)
% 5.43/5.61          | (r1_tarski @ (sk_D_2 @ X34) @ sk_B))),
% 5.43/5.61      inference('simpl_trail', [status(thm)], ['113', '115'])).
% 5.43/5.61  thf('117', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['6', '7'])).
% 5.43/5.61  thf('118', plain,
% 5.43/5.61      (![X34 : $i]:
% 5.43/5.61         ((r1_tarski @ (sk_D_2 @ X34) @ sk_B) | ~ (r2_hidden @ X34 @ sk_B))),
% 5.43/5.61      inference('clc', [status(thm)], ['116', '117'])).
% 5.43/5.61  thf('119', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ 
% 5.43/5.61           (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['112', '118'])).
% 5.43/5.61  thf('120', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (m1_subset_1 @ 
% 5.43/5.61           (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ 
% 5.43/5.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['92', '99'])).
% 5.43/5.61  thf(t48_tops_1, axiom,
% 5.43/5.61    (![A:$i]:
% 5.43/5.61     ( ( l1_pre_topc @ A ) =>
% 5.43/5.61       ( ![B:$i]:
% 5.43/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61           ( ![C:$i]:
% 5.43/5.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.43/5.61               ( ( r1_tarski @ B @ C ) =>
% 5.43/5.61                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.43/5.61  thf('121', plain,
% 5.43/5.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.43/5.61          | ~ (r1_tarski @ X17 @ X19)
% 5.43/5.61          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ (k1_tops_1 @ X18 @ X19))
% 5.43/5.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 5.43/5.61          | ~ (l1_pre_topc @ X18))),
% 5.43/5.61      inference('cnf', [status(esa)], [t48_tops_1])).
% 5.43/5.61  thf('122', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | ~ (l1_pre_topc @ sk_A)
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61          | (r1_tarski @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ 
% 5.43/5.61              (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ X0))
% 5.43/5.61          | ~ (r1_tarski @ 
% 5.43/5.61               (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ X0))),
% 5.43/5.61      inference('sup-', [status(thm)], ['120', '121'])).
% 5.43/5.61  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('124', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61          | (r1_tarski @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ 
% 5.43/5.61              (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61             (k1_tops_1 @ sk_A @ X0))
% 5.43/5.61          | ~ (r1_tarski @ 
% 5.43/5.61               (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)) @ X0))),
% 5.43/5.61      inference('demod', [status(thm)], ['122', '123'])).
% 5.43/5.61  thf('125', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['119', '124'])).
% 5.43/5.61  thf('126', plain,
% 5.43/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('127', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('demod', [status(thm)], ['125', '126'])).
% 5.43/5.61  thf('128', plain,
% 5.43/5.61      (((r1_tarski @ 
% 5.43/5.61         (k1_tops_1 @ sk_A @ 
% 5.43/5.61          (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61         (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('simplify', [status(thm)], ['127'])).
% 5.43/5.61  thf('129', plain,
% 5.43/5.61      (![X9 : $i, X11 : $i]:
% 5.43/5.61         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 5.43/5.61      inference('cnf', [status(esa)], [t3_subset])).
% 5.43/5.61  thf('130', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (m1_subset_1 @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ 
% 5.43/5.61            (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B))) @ 
% 5.43/5.61           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['128', '129'])).
% 5.43/5.61  thf(l3_subset_1, axiom,
% 5.43/5.61    (![A:$i,B:$i]:
% 5.43/5.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.43/5.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.43/5.61  thf('131', plain,
% 5.43/5.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.43/5.61         (~ (r2_hidden @ X3 @ X4)
% 5.43/5.61          | (r2_hidden @ X3 @ X5)
% 5.43/5.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 5.43/5.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.43/5.61  thf('132', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | ~ (r2_hidden @ X0 @ 
% 5.43/5.61               (k1_tops_1 @ sk_A @ 
% 5.43/5.61                (sk_D_2 @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B)))))),
% 5.43/5.61      inference('sup-', [status(thm)], ['130', '131'])).
% 5.43/5.61  thf('133', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61           (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['111', '132'])).
% 5.43/5.61  thf('134', plain,
% 5.43/5.61      (((r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B @ sk_B) @ 
% 5.43/5.61         (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('simplify', [status(thm)], ['133'])).
% 5.43/5.61  thf('135', plain,
% 5.43/5.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 5.43/5.61      inference('sup-', [status(thm)], ['74', '75'])).
% 5.43/5.61  thf('136', plain,
% 5.43/5.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 5.43/5.61          | (r1_tarski @ X8 @ X6)
% 5.43/5.61          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 5.43/5.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 5.43/5.61      inference('cnf', [status(esa)], [t7_subset_1])).
% 5.43/5.61  thf('137', plain,
% 5.43/5.61      (![X0 : $i]:
% 5.43/5.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 5.43/5.61          | ~ (r2_hidden @ (sk_D @ (k1_tops_1 @ sk_A @ sk_B) @ X0 @ sk_B) @ 
% 5.43/5.61               (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61          | (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['135', '136'])).
% 5.43/5.61  thf('138', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))),
% 5.43/5.61      inference('sup-', [status(thm)], ['134', '137'])).
% 5.43/5.61  thf('139', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.43/5.61      inference('sup-', [status(thm)], ['71', '72'])).
% 5.43/5.61  thf('140', plain,
% 5.43/5.61      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.43/5.61        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.43/5.61      inference('demod', [status(thm)], ['138', '139'])).
% 5.43/5.61  thf('141', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 5.43/5.61      inference('simplify', [status(thm)], ['140'])).
% 5.43/5.61  thf('142', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 5.43/5.61      inference('demod', [status(thm)], ['70', '141'])).
% 5.43/5.61  thf('143', plain, (((v3_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 5.43/5.61      inference('demod', [status(thm)], ['63', '142'])).
% 5.43/5.61  thf('144', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 5.43/5.61      inference('simplify', [status(thm)], ['143'])).
% 5.43/5.61  thf('145', plain, ($false), inference('demod', [status(thm)], ['48', '144'])).
% 5.43/5.61  
% 5.43/5.61  % SZS output end Refutation
% 5.43/5.61  
% 5.43/5.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
