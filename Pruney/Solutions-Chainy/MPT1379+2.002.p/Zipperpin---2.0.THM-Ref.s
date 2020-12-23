%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fCi5TzDH0G

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:48 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 411 expanded)
%              Number of leaves         :   25 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          : 1801 (7961 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t4_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                  <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                    <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_connsp_2])).

thf('0',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) )
                = ( k1_tops_1 @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_tops_1 @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X19 ) )
        = ( k1_tops_1 @ X18 @ ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['32','39','40'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('61',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['32','39','40'])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('78',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('80',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['32','39','40'])).

thf('81',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) )
   <= ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','107'])).

thf('109',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['80','108'])).

thf('110',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['110'])).

thf('112',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['110'])).

thf('115',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['110'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('124',plain,(
    r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['121','128'])).

thf('130',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_D_1 ) @ sk_A @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('141',plain,
    ( ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('142',plain,
    ( ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','78','79','143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fCi5TzDH0G
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.46/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.69  % Solved by: fo/fo7.sh
% 1.46/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.69  % done 2015 iterations in 1.237s
% 1.46/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.69  % SZS output start Refutation
% 1.46/1.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.46/1.69  thf(sk_C_type, type, sk_C: $i).
% 1.46/1.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.46/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.46/1.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.46/1.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.46/1.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.46/1.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.46/1.69  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.46/1.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.46/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.46/1.70  thf(t4_connsp_2, conjecture,
% 1.46/1.70    (![A:$i]:
% 1.46/1.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.46/1.70       ( ![B:$i]:
% 1.46/1.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.46/1.70           ( ![C:$i]:
% 1.46/1.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.46/1.70               ( ![D:$i]:
% 1.46/1.70                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.46/1.70                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.46/1.70                       ( m1_connsp_2 @ D @ A @ B ) ) <=>
% 1.46/1.70                     ( m1_connsp_2 @
% 1.46/1.70                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 1.46/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.70    (~( ![A:$i]:
% 1.46/1.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.46/1.70            ( l1_pre_topc @ A ) ) =>
% 1.46/1.70          ( ![B:$i]:
% 1.46/1.70            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.46/1.70              ( ![C:$i]:
% 1.46/1.70                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.70                  ( ![D:$i]:
% 1.53/1.70                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.70                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 1.53/1.70                          ( m1_connsp_2 @ D @ A @ B ) ) <=>
% 1.53/1.70                        ( m1_connsp_2 @
% 1.53/1.70                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 1.53/1.70    inference('cnf.neg', [status(esa)], [t4_connsp_2])).
% 1.53/1.70  thf('0', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B)
% 1.53/1.70        | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('1', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)) | 
% 1.53/1.70       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B))),
% 1.53/1.70      inference('split', [status(esa)], ['0'])).
% 1.53/1.70  thf('2', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(redefinition_k9_subset_1, axiom,
% 1.53/1.70    (![A:$i,B:$i,C:$i]:
% 1.53/1.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.70       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.53/1.70  thf('3', plain,
% 1.53/1.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.53/1.70         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 1.53/1.70          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.53/1.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.53/1.70  thf('4', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 1.53/1.70           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 1.53/1.70      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.70  thf('5', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B)
% 1.53/1.70        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('6', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['5'])).
% 1.53/1.70  thf('7', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup+', [status(thm)], ['4', '6'])).
% 1.53/1.70  thf('8', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(t3_subset, axiom,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.53/1.70  thf('9', plain,
% 1.53/1.70      (![X12 : $i, X13 : $i]:
% 1.53/1.70         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.53/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.70  thf('10', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['8', '9'])).
% 1.53/1.70  thf(t108_xboole_1, axiom,
% 1.53/1.70    (![A:$i,B:$i,C:$i]:
% 1.53/1.70     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 1.53/1.70  thf('11', plain,
% 1.53/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.53/1.70         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k3_xboole_0 @ X6 @ X8) @ X7))),
% 1.53/1.70      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.53/1.70  thf('12', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.70  thf('13', plain,
% 1.53/1.70      (![X12 : $i, X14 : $i]:
% 1.53/1.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.53/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.70  thf('14', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 1.53/1.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['12', '13'])).
% 1.53/1.70  thf(d1_connsp_2, axiom,
% 1.53/1.70    (![A:$i]:
% 1.53/1.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.70       ( ![B:$i]:
% 1.53/1.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.53/1.70           ( ![C:$i]:
% 1.53/1.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.70               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 1.53/1.70                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.53/1.70  thf('15', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('16', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))
% 1.53/1.70          | ~ (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A @ X1)
% 1.53/1.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['14', '15'])).
% 1.53/1.70  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('19', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (r2_hidden @ X1 @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))
% 1.53/1.70          | ~ (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A @ X1)
% 1.53/1.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.53/1.70  thf('20', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (r2_hidden @ sk_B @ 
% 1.53/1.70            (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['7', '19'])).
% 1.53/1.70  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('22', plain,
% 1.53/1.70      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['20', '21'])).
% 1.53/1.70  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('24', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['22', '23'])).
% 1.53/1.70  thf('25', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('26', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(t46_tops_1, axiom,
% 1.53/1.70    (![A:$i]:
% 1.53/1.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.70       ( ![B:$i]:
% 1.53/1.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.70           ( ![C:$i]:
% 1.53/1.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.70               ( ( k9_subset_1 @
% 1.53/1.70                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 1.53/1.70                   ( k1_tops_1 @ A @ C ) ) =
% 1.53/1.70                 ( k1_tops_1 @
% 1.53/1.70                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 1.53/1.70  thf('27', plain,
% 1.53/1.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.53/1.70          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ (k1_tops_1 @ X18 @ X17) @ 
% 1.53/1.70              (k1_tops_1 @ X18 @ X19))
% 1.53/1.70              = (k1_tops_1 @ X18 @ 
% 1.53/1.70                 (k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X19)))
% 1.53/1.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.53/1.70          | ~ (l1_pre_topc @ X18)
% 1.53/1.70          | ~ (v2_pre_topc @ X18))),
% 1.53/1.70      inference('cnf', [status(esa)], [t46_tops_1])).
% 1.53/1.70  thf('28', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.70          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 1.53/1.70              (k1_tops_1 @ sk_A @ X0))
% 1.53/1.70              = (k1_tops_1 @ sk_A @ 
% 1.53/1.70                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 1.53/1.70      inference('sup-', [status(thm)], ['26', '27'])).
% 1.53/1.70  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('31', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.70          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 1.53/1.70              (k1_tops_1 @ sk_A @ X0))
% 1.53/1.70              = (k1_tops_1 @ sk_A @ 
% 1.53/1.70                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 1.53/1.70      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.53/1.70  thf('32', plain,
% 1.53/1.70      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 1.53/1.70         (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         = (k1_tops_1 @ sk_A @ 
% 1.53/1.70            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['25', '31'])).
% 1.53/1.70  thf('33', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf(dt_k1_tops_1, axiom,
% 1.53/1.70    (![A:$i,B:$i]:
% 1.53/1.70     ( ( ( l1_pre_topc @ A ) & 
% 1.53/1.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.53/1.70       ( m1_subset_1 @
% 1.53/1.70         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.53/1.70  thf('34', plain,
% 1.53/1.70      (![X15 : $i, X16 : $i]:
% 1.53/1.70         (~ (l1_pre_topc @ X15)
% 1.53/1.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.53/1.70          | (m1_subset_1 @ (k1_tops_1 @ X15 @ X16) @ 
% 1.53/1.70             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.53/1.70      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.53/1.70  thf('35', plain,
% 1.53/1.70      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 1.53/1.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.70        | ~ (l1_pre_topc @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['33', '34'])).
% 1.53/1.70  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('37', plain,
% 1.53/1.70      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 1.53/1.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['35', '36'])).
% 1.53/1.70  thf('38', plain,
% 1.53/1.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.53/1.70         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 1.53/1.70          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.53/1.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.53/1.70  thf('39', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.53/1.70           (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70           = (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.70  thf('40', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 1.53/1.70           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 1.53/1.70      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.70  thf('41', plain,
% 1.53/1.70      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))),
% 1.53/1.70      inference('demod', [status(thm)], ['32', '39', '40'])).
% 1.53/1.70  thf(d4_xboole_0, axiom,
% 1.53/1.70    (![A:$i,B:$i,C:$i]:
% 1.53/1.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.53/1.70       ( ![D:$i]:
% 1.53/1.70         ( ( r2_hidden @ D @ C ) <=>
% 1.53/1.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.53/1.70  thf('42', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X4 @ X3)
% 1.53/1.70          | (r2_hidden @ X4 @ X2)
% 1.53/1.70          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.53/1.70  thf('43', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.53/1.70         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['42'])).
% 1.53/1.70  thf('44', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X0 @ 
% 1.53/1.70             (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['41', '43'])).
% 1.53/1.70  thf('45', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['24', '44'])).
% 1.53/1.70  thf('46', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('47', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('48', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['46', '47'])).
% 1.53/1.70  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('51', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.53/1.70  thf('52', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['45', '51'])).
% 1.53/1.70  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('54', plain,
% 1.53/1.70      ((((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['52', '53'])).
% 1.53/1.70  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('56', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['54', '55'])).
% 1.53/1.70  thf('57', plain,
% 1.53/1.70      ((~ (m1_connsp_2 @ 
% 1.53/1.70           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 1.53/1.70        | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)
% 1.53/1.70        | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('58', plain,
% 1.53/1.70      ((~ (m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 1.53/1.70         <= (~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['57'])).
% 1.53/1.70  thf('59', plain,
% 1.53/1.70      (~
% 1.53/1.70       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B)) | 
% 1.53/1.70       ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 1.53/1.70      inference('sup-', [status(thm)], ['56', '58'])).
% 1.53/1.70  thf('60', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['22', '23'])).
% 1.53/1.70  thf('61', plain,
% 1.53/1.70      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))),
% 1.53/1.70      inference('demod', [status(thm)], ['32', '39', '40'])).
% 1.53/1.70  thf('62', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X4 @ X3)
% 1.53/1.70          | (r2_hidden @ X4 @ X1)
% 1.53/1.70          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.53/1.70  thf('63', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.53/1.70         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['62'])).
% 1.53/1.70  thf('64', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X0 @ 
% 1.53/1.70             (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['61', '63'])).
% 1.53/1.70  thf('65', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['60', '64'])).
% 1.53/1.70  thf('66', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('67', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('68', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['66', '67'])).
% 1.53/1.70  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('71', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.53/1.70  thf('72', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['65', '71'])).
% 1.53/1.70  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('74', plain,
% 1.53/1.70      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['72', '73'])).
% 1.53/1.70  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('76', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['74', '75'])).
% 1.53/1.70  thf('77', plain,
% 1.53/1.70      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 1.53/1.70         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['57'])).
% 1.53/1.70  thf('78', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 1.53/1.70       ~
% 1.53/1.70       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B))),
% 1.53/1.70      inference('sup-', [status(thm)], ['76', '77'])).
% 1.53/1.70  thf('79', plain,
% 1.53/1.70      (~
% 1.53/1.70       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B)) | 
% 1.53/1.70       ~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)) | 
% 1.53/1.70       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 1.53/1.70      inference('split', [status(esa)], ['57'])).
% 1.53/1.70  thf('80', plain,
% 1.53/1.70      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         = (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1)))),
% 1.53/1.70      inference('demod', [status(thm)], ['32', '39', '40'])).
% 1.53/1.70  thf('81', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['5'])).
% 1.53/1.70  thf('82', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('83', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('84', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 1.53/1.70          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['82', '83'])).
% 1.53/1.70  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('87', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 1.53/1.70          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.53/1.70  thf('88', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 1.53/1.70         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['81', '87'])).
% 1.53/1.70  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('90', plain,
% 1.53/1.70      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['88', '89'])).
% 1.53/1.70  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('92', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['90', '91'])).
% 1.53/1.70  thf('93', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['0'])).
% 1.53/1.70  thf('94', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('95', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('96', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['94', '95'])).
% 1.53/1.70  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('99', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70          | ~ (m1_connsp_2 @ sk_D_1 @ sk_A @ X0)
% 1.53/1.70          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.53/1.70  thf('100', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['93', '99'])).
% 1.53/1.70  thf('101', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('102', plain,
% 1.53/1.70      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1))
% 1.53/1.70         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['100', '101'])).
% 1.53/1.70  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('104', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_D_1)))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['102', '103'])).
% 1.53/1.70  thf('105', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.53/1.70         (~ (r2_hidden @ X0 @ X1)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ X2)
% 1.53/1.70          | (r2_hidden @ X0 @ X3)
% 1.53/1.70          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.53/1.70  thf('106', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.70         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 1.53/1.70          | ~ (r2_hidden @ X0 @ X2)
% 1.53/1.70          | ~ (r2_hidden @ X0 @ X1))),
% 1.53/1.70      inference('simplify', [status(thm)], ['105'])).
% 1.53/1.70  thf('107', plain,
% 1.53/1.70      ((![X0 : $i]:
% 1.53/1.70          (~ (r2_hidden @ sk_B @ X0)
% 1.53/1.70           | (r2_hidden @ sk_B @ 
% 1.53/1.70              (k3_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_D_1)))))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['104', '106'])).
% 1.53/1.70  thf('108', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ 
% 1.53/1.70         (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_D_1))))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 1.53/1.70             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['92', '107'])).
% 1.53/1.70  thf('109', plain,
% 1.53/1.70      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_D_1))))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 1.53/1.70             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup+', [status(thm)], ['80', '108'])).
% 1.53/1.70  thf('110', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.53/1.70         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.53/1.70          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.53/1.70          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.53/1.70  thf('111', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('eq_fact', [status(thm)], ['110'])).
% 1.53/1.70  thf('112', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.53/1.70         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['42'])).
% 1.53/1.70  thf('113', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.70         (((k3_xboole_0 @ X1 @ X0)
% 1.53/1.70            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.53/1.70          | (r2_hidden @ 
% 1.53/1.70             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.53/1.70             X0))),
% 1.53/1.70      inference('sup-', [status(thm)], ['111', '112'])).
% 1.53/1.70  thf('114', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('eq_fact', [status(thm)], ['110'])).
% 1.53/1.70  thf('115', plain,
% 1.53/1.70      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.53/1.70         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.53/1.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.53/1.70  thf('116', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['114', '115'])).
% 1.53/1.70  thf('117', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['116'])).
% 1.53/1.70  thf('118', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.53/1.70          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('eq_fact', [status(thm)], ['110'])).
% 1.53/1.70  thf('119', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.53/1.70          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.53/1.70      inference('clc', [status(thm)], ['117', '118'])).
% 1.53/1.70  thf('120', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         (((k3_xboole_0 @ X1 @ X0)
% 1.53/1.70            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.53/1.70          | ((k3_xboole_0 @ X1 @ X0)
% 1.53/1.70              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.53/1.70      inference('sup-', [status(thm)], ['113', '119'])).
% 1.53/1.70  thf('121', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((k3_xboole_0 @ X1 @ X0)
% 1.53/1.70           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.53/1.70      inference('simplify', [status(thm)], ['120'])).
% 1.53/1.70  thf('122', plain,
% 1.53/1.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('123', plain,
% 1.53/1.70      (![X12 : $i, X13 : $i]:
% 1.53/1.70         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.53/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.70  thf('124', plain, ((r1_tarski @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['122', '123'])).
% 1.53/1.70  thf('125', plain,
% 1.53/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.53/1.70         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k3_xboole_0 @ X6 @ X8) @ X7))),
% 1.53/1.70      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.53/1.70  thf('126', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (r1_tarski @ (k3_xboole_0 @ sk_D_1 @ X0) @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('sup-', [status(thm)], ['124', '125'])).
% 1.53/1.70  thf('127', plain,
% 1.53/1.70      (![X12 : $i, X14 : $i]:
% 1.53/1.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.53/1.70      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.70  thf('128', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (m1_subset_1 @ (k3_xboole_0 @ sk_D_1 @ X0) @ 
% 1.53/1.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['126', '127'])).
% 1.53/1.70  thf('129', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_D_1) @ 
% 1.53/1.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup+', [status(thm)], ['121', '128'])).
% 1.53/1.70  thf('130', plain,
% 1.53/1.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.53/1.70         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 1.53/1.70          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.53/1.70          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 1.53/1.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.53/1.70          | ~ (l1_pre_topc @ X21)
% 1.53/1.70          | ~ (v2_pre_topc @ X21)
% 1.53/1.70          | (v2_struct_0 @ X21))),
% 1.53/1.70      inference('cnf', [status(esa)], [d1_connsp_2])).
% 1.53/1.70  thf('131', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | ~ (v2_pre_topc @ sk_A)
% 1.53/1.70          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 1.53/1.70          | ~ (r2_hidden @ X1 @ 
% 1.53/1.70               (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 1.53/1.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['129', '130'])).
% 1.53/1.70  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('134', plain,
% 1.53/1.70      (![X0 : $i, X1 : $i]:
% 1.53/1.70         ((v2_struct_0 @ sk_A)
% 1.53/1.70          | (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_D_1) @ sk_A @ X1)
% 1.53/1.70          | ~ (r2_hidden @ X1 @ 
% 1.53/1.70               (k1_tops_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_D_1)))
% 1.53/1.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.70      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.53/1.70  thf('135', plain,
% 1.53/1.70      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.53/1.70         | (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 1.53/1.70             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['109', '134'])).
% 1.53/1.70  thf('136', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('137', plain,
% 1.53/1.70      ((((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 1.53/1.70         | (v2_struct_0 @ sk_A)))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 1.53/1.70             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('demod', [status(thm)], ['135', '136'])).
% 1.53/1.70  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.70  thf('139', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 1.53/1.70         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 1.53/1.70             ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B)))),
% 1.53/1.70      inference('clc', [status(thm)], ['137', '138'])).
% 1.53/1.70  thf('140', plain,
% 1.53/1.70      (![X0 : $i]:
% 1.53/1.70         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D_1)
% 1.53/1.70           = (k3_xboole_0 @ X0 @ sk_D_1))),
% 1.53/1.70      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.70  thf('141', plain,
% 1.53/1.70      ((~ (m1_connsp_2 @ 
% 1.53/1.70           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 1.53/1.70         <= (~
% 1.53/1.70             ((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('split', [status(esa)], ['57'])).
% 1.53/1.70  thf('142', plain,
% 1.53/1.70      ((~ (m1_connsp_2 @ (k3_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B))
% 1.53/1.70         <= (~
% 1.53/1.70             ((m1_connsp_2 @ 
% 1.53/1.70               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ sk_A @ 
% 1.53/1.70               sk_B)))),
% 1.53/1.70      inference('sup-', [status(thm)], ['140', '141'])).
% 1.53/1.70  thf('143', plain,
% 1.53/1.70      (((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B)) | 
% 1.53/1.70       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 1.53/1.70       ~ ((m1_connsp_2 @ sk_D_1 @ sk_A @ sk_B))),
% 1.53/1.70      inference('sup-', [status(thm)], ['139', '142'])).
% 1.53/1.70  thf('144', plain,
% 1.53/1.70      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 1.53/1.70       ((m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 1.53/1.70         sk_A @ sk_B))),
% 1.53/1.70      inference('split', [status(esa)], ['5'])).
% 1.53/1.70  thf('145', plain, ($false),
% 1.53/1.70      inference('sat_resolution*', [status(thm)],
% 1.53/1.70                ['1', '59', '78', '79', '143', '144'])).
% 1.53/1.70  
% 1.53/1.70  % SZS output end Refutation
% 1.53/1.70  
% 1.53/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
