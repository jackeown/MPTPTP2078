%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9YW3Sncof

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 513 expanded)
%              Number of leaves         :   23 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  925 (9369 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['8'])).

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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 )
        | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_D @ X0 )
        | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_D @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('48',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('52',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X20 ) ) ),
    inference(demod,[status(thm)],['48','49','55'])).

thf('57',plain,
    ( ~ ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X20 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('59',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['21','57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('61',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['21','57','60'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('63',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['21','57','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['21','57','64'])).

thf('66',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['19','59','61','63','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m1_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('77',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['21','57'])).

thf('78',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['75','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9YW3Sncof
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 475 iterations in 0.176s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.63  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(t8_connsp_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.46/0.63                 ( ?[D:$i]:
% 0.46/0.63                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.46/0.63                     ( v3_pre_topc @ D @ A ) & 
% 0.46/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.46/0.63                    ( ?[D:$i]:
% 0.46/0.63                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.46/0.63                        ( v3_pre_topc @ D @ A ) & 
% 0.46/0.63                        ( m1_subset_1 @
% 0.46/0.63                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.46/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.46/0.63      inference('split', [status(esa)], ['1'])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (((r1_tarski @ sk_D @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 0.46/0.63      inference('split', [status(esa)], ['3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['6'])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('split', [status(esa)], ['8'])).
% 0.46/0.63  thf(t56_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.63          | ~ (v3_pre_topc @ X14 @ X15)
% 0.46/0.63          | ~ (r1_tarski @ X14 @ X16)
% 0.46/0.63          | (r1_tarski @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.46/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.63          | ~ (l1_pre_topc @ X15))),
% 0.46/0.63      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (l1_pre_topc @ sk_A)
% 0.46/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (r1_tarski @ sk_D @ X0)
% 0.46/0.63           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.46/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (r1_tarski @ sk_D @ X0)
% 0.46/0.63           | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.46/0.63         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          (~ (r1_tarski @ sk_D @ X0)
% 0.46/0.63           | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.63           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63         | ~ (r1_tarski @ sk_D @ sk_C_1)))
% 0.46/0.63         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.46/0.63         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '15'])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.63          | (r2_hidden @ X0 @ X2)
% 0.46/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.46/0.63         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.46/0.63         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.46/0.63             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 0.46/0.63             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.46/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X20 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63          | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63          | ~ (r2_hidden @ sk_B @ X20)
% 0.46/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.46/0.63       (![X20 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63           | ~ (r2_hidden @ sk_B @ X20)))),
% 0.46/0.63      inference('split', [status(esa)], ['20'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.46/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['1'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d1_connsp_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.46/0.63                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.46/0.63          | ~ (m1_connsp_2 @ X19 @ X18 @ X17)
% 0.46/0.63          | (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.46/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.63          | ~ (l1_pre_topc @ X18)
% 0.46/0.63          | ~ (v2_pre_topc @ X18)
% 0.46/0.63          | (v2_struct_0 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_A)
% 0.46/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_A)
% 0.46/0.63          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.46/0.63         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.63  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.46/0.63         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('clc', [status(thm)], ['31', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t3_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i]:
% 0.46/0.63         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('36', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t44_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.63          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.46/0.63          | ~ (l1_pre_topc @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('41', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.46/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf(t1_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.63       ( r1_tarski @ A @ C ) ))).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X4 @ X5)
% 0.46/0.63          | ~ (r1_tarski @ X5 @ X6)
% 0.46/0.63          | (r1_tarski @ X4 @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.46/0.63          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '43'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X7 : $i, X9 : $i]:
% 0.46/0.63         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.46/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      ((![X20 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63           | ~ (r2_hidden @ sk_B @ X20)))
% 0.46/0.63         <= ((![X20 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.46/0.63      inference('split', [status(esa)], ['20'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.46/0.63         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.46/0.63         <= ((![X20 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.63  thf('49', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.46/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(fc9_tops_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X10)
% 0.46/0.63          | ~ (v2_pre_topc @ X10)
% 0.46/0.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.63          | (v3_pre_topc @ (k1_tops_1 @ X10 @ X11) @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.63  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('55', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.46/0.63         <= ((![X20 : $i]:
% 0.46/0.63                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63                 | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63                 | ~ (r2_hidden @ sk_B @ X20))))),
% 0.46/0.63      inference('demod', [status(thm)], ['48', '49', '55'])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (~
% 0.46/0.63       (![X20 : $i]:
% 0.46/0.63          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.46/0.63           | ~ (r1_tarski @ X20 @ sk_C_1)
% 0.46/0.63           | ~ (r2_hidden @ sk_B @ X20))) | 
% 0.46/0.63       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['33', '56'])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('split', [status(esa)], ['1'])).
% 0.46/0.63  thf('59', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['21', '57', '58'])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (((r1_tarski @ sk_D @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('split', [status(esa)], ['3'])).
% 0.46/0.63  thf('61', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['21', '57', '60'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('split', [status(esa)], ['6'])).
% 0.46/0.63  thf('63', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['21', '57', '62'])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.46/0.63       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('split', [status(esa)], ['8'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['21', '57', '64'])).
% 0.46/0.63  thf('66', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['19', '59', '61', '63', '65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.46/0.63          | ~ (r2_hidden @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.46/0.63          | (m1_connsp_2 @ X19 @ X18 @ X17)
% 0.46/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.63          | ~ (l1_pre_topc @ X18)
% 0.46/0.63          | ~ (v2_pre_topc @ X18)
% 0.46/0.63          | (v2_struct_0 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_A)
% 0.46/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_struct_0 @ sk_A)
% 0.46/0.63          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.63        | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '72'])).
% 0.46/0.63  thf('74', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.46/0.63         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['20'])).
% 0.46/0.63  thf('77', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['21', '57'])).
% 0.46/0.63  thf('78', plain, (~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.63      inference('clc', [status(thm)], ['75', '78'])).
% 0.46/0.63  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
