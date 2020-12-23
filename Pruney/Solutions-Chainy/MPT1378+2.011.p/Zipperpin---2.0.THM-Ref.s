%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gezbshsAMH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:46 EST 2020

% Result     : Theorem 9.92s
% Output     : Refutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 153 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  828 (2794 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t3_connsp_2,conjecture,(
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
                   => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

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
                     => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X7 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) @ ( k1_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) ) @ ( k1_tops_1 @ X19 @ ( k4_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_tops_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','35','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('62',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['59','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gezbshsAMH
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 9.92/10.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.92/10.11  % Solved by: fo/fo7.sh
% 9.92/10.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.92/10.11  % done 4544 iterations in 9.661s
% 9.92/10.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.92/10.11  % SZS output start Refutation
% 9.92/10.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.92/10.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 9.92/10.11  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 9.92/10.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.92/10.11  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.92/10.11  thf(sk_B_type, type, sk_B: $i).
% 9.92/10.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.92/10.11  thf(sk_D_1_type, type, sk_D_1: $i).
% 9.92/10.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.92/10.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.92/10.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.92/10.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.92/10.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.92/10.11  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 9.92/10.11  thf(sk_A_type, type, sk_A: $i).
% 9.92/10.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 9.92/10.11  thf(t3_connsp_2, conjecture,
% 9.92/10.11    (![A:$i]:
% 9.92/10.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.92/10.11       ( ![B:$i]:
% 9.92/10.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 9.92/10.11           ( ![C:$i]:
% 9.92/10.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11               ( ![D:$i]:
% 9.92/10.11                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 9.92/10.11                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 9.92/10.11                     ( m1_connsp_2 @
% 9.92/10.11                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 9.92/10.11  thf(zf_stmt_0, negated_conjecture,
% 9.92/10.11    (~( ![A:$i]:
% 9.92/10.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 9.92/10.11            ( l1_pre_topc @ A ) ) =>
% 9.92/10.11          ( ![B:$i]:
% 9.92/10.11            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 9.92/10.11              ( ![C:$i]:
% 9.92/10.11                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11                  ( ![D:$i]:
% 9.92/10.11                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 9.92/10.11                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 9.92/10.11                        ( m1_connsp_2 @
% 9.92/10.11                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 9.92/10.11    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 9.92/10.11  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('2', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf(d1_connsp_2, axiom,
% 9.92/10.11    (![A:$i]:
% 9.92/10.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.92/10.11       ( ![B:$i]:
% 9.92/10.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 9.92/10.11           ( ![C:$i]:
% 9.92/10.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 9.92/10.11                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 9.92/10.11  thf('3', plain,
% 9.92/10.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 9.92/10.11          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 9.92/10.11          | (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 9.92/10.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 9.92/10.11          | ~ (l1_pre_topc @ X22)
% 9.92/10.11          | ~ (v2_pre_topc @ X22)
% 9.92/10.11          | (v2_struct_0 @ X22))),
% 9.92/10.11      inference('cnf', [status(esa)], [d1_connsp_2])).
% 9.92/10.11  thf('4', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((v2_struct_0 @ sk_A)
% 9.92/10.11          | ~ (v2_pre_topc @ sk_A)
% 9.92/10.11          | ~ (l1_pre_topc @ sk_A)
% 9.92/10.11          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 9.92/10.11          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['2', '3'])).
% 9.92/10.11  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('7', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((v2_struct_0 @ sk_A)
% 9.92/10.11          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 9.92/10.11          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('demod', [status(thm)], ['4', '5', '6'])).
% 9.92/10.11  thf('8', plain,
% 9.92/10.11      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 9.92/10.11        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 9.92/10.11        | (v2_struct_0 @ sk_A))),
% 9.92/10.11      inference('sup-', [status(thm)], ['1', '7'])).
% 9.92/10.11  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('10', plain,
% 9.92/10.11      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 9.92/10.11      inference('demod', [status(thm)], ['8', '9'])).
% 9.92/10.11  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 9.92/10.11      inference('clc', [status(thm)], ['10', '11'])).
% 9.92/10.11  thf(d3_xboole_0, axiom,
% 9.92/10.11    (![A:$i,B:$i,C:$i]:
% 9.92/10.11     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 9.92/10.11       ( ![D:$i]:
% 9.92/10.11         ( ( r2_hidden @ D @ C ) <=>
% 9.92/10.11           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 9.92/10.11  thf('13', plain,
% 9.92/10.11      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 9.92/10.11         (~ (r2_hidden @ X4 @ X7)
% 9.92/10.11          | (r2_hidden @ X4 @ X6)
% 9.92/10.11          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 9.92/10.11      inference('cnf', [status(esa)], [d3_xboole_0])).
% 9.92/10.11  thf('14', plain,
% 9.92/10.11      (![X4 : $i, X5 : $i, X7 : $i]:
% 9.92/10.11         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X7))),
% 9.92/10.11      inference('simplify', [status(thm)], ['13'])).
% 9.92/10.11  thf('15', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         (r2_hidden @ sk_B @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))),
% 9.92/10.11      inference('sup-', [status(thm)], ['12', '14'])).
% 9.92/10.11  thf('16', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('17', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf(t49_tops_1, axiom,
% 9.92/10.11    (![A:$i]:
% 9.92/10.11     ( ( l1_pre_topc @ A ) =>
% 9.92/10.11       ( ![B:$i]:
% 9.92/10.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11           ( ![C:$i]:
% 9.92/10.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.92/10.11               ( r1_tarski @
% 9.92/10.11                 ( k4_subset_1 @
% 9.92/10.11                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 9.92/10.11                   ( k1_tops_1 @ A @ C ) ) @ 
% 9.92/10.11                 ( k1_tops_1 @
% 9.92/10.11                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 9.92/10.11  thf('18', plain,
% 9.92/10.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 9.92/10.11          | (r1_tarski @ 
% 9.92/10.11             (k4_subset_1 @ (u1_struct_0 @ X19) @ (k1_tops_1 @ X19 @ X18) @ 
% 9.92/10.11              (k1_tops_1 @ X19 @ X20)) @ 
% 9.92/10.11             (k1_tops_1 @ X19 @ (k4_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20)))
% 9.92/10.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 9.92/10.11          | ~ (l1_pre_topc @ X19))),
% 9.92/10.11      inference('cnf', [status(esa)], [t49_tops_1])).
% 9.92/10.11  thf('19', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         (~ (l1_pre_topc @ sk_A)
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.92/10.11          | (r1_tarski @ 
% 9.92/10.11             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.92/10.11              (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0)) @ 
% 9.92/10.11             (k1_tops_1 @ sk_A @ 
% 9.92/10.11              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 9.92/10.11      inference('sup-', [status(thm)], ['17', '18'])).
% 9.92/10.11  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('21', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.92/10.11          | (r1_tarski @ 
% 9.92/10.11             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.92/10.11              (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0)) @ 
% 9.92/10.11             (k1_tops_1 @ sk_A @ 
% 9.92/10.11              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 9.92/10.11      inference('demod', [status(thm)], ['19', '20'])).
% 9.92/10.11  thf('22', plain,
% 9.92/10.11      ((r1_tarski @ 
% 9.92/10.11        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11         (k1_tops_1 @ sk_A @ sk_D_1)) @ 
% 9.92/10.11        (k1_tops_1 @ sk_A @ 
% 9.92/10.11         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['16', '21'])).
% 9.92/10.11  thf('23', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf(dt_k1_tops_1, axiom,
% 9.92/10.11    (![A:$i,B:$i]:
% 9.92/10.11     ( ( ( l1_pre_topc @ A ) & 
% 9.92/10.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.92/10.11       ( m1_subset_1 @
% 9.92/10.11         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.92/10.11  thf('24', plain,
% 9.92/10.11      (![X16 : $i, X17 : $i]:
% 9.92/10.11         (~ (l1_pre_topc @ X16)
% 9.92/10.11          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 9.92/10.11          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 9.92/10.11             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 9.92/10.11      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 9.92/10.11  thf('25', plain,
% 9.92/10.11      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 9.92/10.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.92/10.11        | ~ (l1_pre_topc @ sk_A))),
% 9.92/10.11      inference('sup-', [status(thm)], ['23', '24'])).
% 9.92/10.11  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('27', plain,
% 9.92/10.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D_1) @ 
% 9.92/10.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('demod', [status(thm)], ['25', '26'])).
% 9.92/10.11  thf('28', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('29', plain,
% 9.92/10.11      (![X16 : $i, X17 : $i]:
% 9.92/10.11         (~ (l1_pre_topc @ X16)
% 9.92/10.11          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 9.92/10.11          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 9.92/10.11             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 9.92/10.11      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 9.92/10.11  thf('30', plain,
% 9.92/10.11      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.92/10.11        | ~ (l1_pre_topc @ sk_A))),
% 9.92/10.11      inference('sup-', [status(thm)], ['28', '29'])).
% 9.92/10.11  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('32', plain,
% 9.92/10.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('demod', [status(thm)], ['30', '31'])).
% 9.92/10.11  thf(redefinition_k4_subset_1, axiom,
% 9.92/10.11    (![A:$i,B:$i,C:$i]:
% 9.92/10.11     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.92/10.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.92/10.11       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.92/10.11  thf('33', plain,
% 9.92/10.11      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 9.92/10.11          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 9.92/10.11          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 9.92/10.11      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.92/10.11  thf('34', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11            X0) = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0))
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.92/10.11      inference('sup-', [status(thm)], ['32', '33'])).
% 9.92/10.11  thf('35', plain,
% 9.92/10.11      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11         (k1_tops_1 @ sk_A @ sk_D_1))
% 9.92/10.11         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11            (k1_tops_1 @ sk_A @ sk_D_1)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['27', '34'])).
% 9.92/10.11  thf('36', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('37', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('38', plain,
% 9.92/10.11      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 9.92/10.11          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 9.92/10.11          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 9.92/10.11      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.92/10.11  thf('39', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 9.92/10.11            = (k2_xboole_0 @ sk_C_1 @ X0))
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.92/10.11      inference('sup-', [status(thm)], ['37', '38'])).
% 9.92/10.11  thf('40', plain,
% 9.92/10.11      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 9.92/10.11         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 9.92/10.11      inference('sup-', [status(thm)], ['36', '39'])).
% 9.92/10.11  thf('41', plain,
% 9.92/10.11      ((r1_tarski @ 
% 9.92/10.11        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11         (k1_tops_1 @ sk_A @ sk_D_1)) @ 
% 9.92/10.11        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 9.92/10.11      inference('demod', [status(thm)], ['22', '35', '40'])).
% 9.92/10.11  thf(d3_tarski, axiom,
% 9.92/10.11    (![A:$i,B:$i]:
% 9.92/10.11     ( ( r1_tarski @ A @ B ) <=>
% 9.92/10.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.92/10.11  thf('42', plain,
% 9.92/10.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.92/10.11         (~ (r2_hidden @ X0 @ X1)
% 9.92/10.11          | (r2_hidden @ X0 @ X2)
% 9.92/10.11          | ~ (r1_tarski @ X1 @ X2))),
% 9.92/10.11      inference('cnf', [status(esa)], [d3_tarski])).
% 9.92/10.11  thf('43', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((r2_hidden @ X0 @ 
% 9.92/10.11           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 9.92/10.11          | ~ (r2_hidden @ X0 @ 
% 9.92/10.11               (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 9.92/10.11                (k1_tops_1 @ sk_A @ sk_D_1))))),
% 9.92/10.11      inference('sup-', [status(thm)], ['41', '42'])).
% 9.92/10.11  thf('44', plain,
% 9.92/10.11      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['15', '43'])).
% 9.92/10.11  thf('45', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('46', plain,
% 9.92/10.11      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf(dt_k4_subset_1, axiom,
% 9.92/10.11    (![A:$i,B:$i,C:$i]:
% 9.92/10.11     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.92/10.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.92/10.11       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.92/10.11  thf('47', plain,
% 9.92/10.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.92/10.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 9.92/10.11          | (m1_subset_1 @ (k4_subset_1 @ X11 @ X10 @ X12) @ 
% 9.92/10.11             (k1_zfmisc_1 @ X11)))),
% 9.92/10.11      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 9.92/10.11  thf('48', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0) @ 
% 9.92/10.11           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.92/10.11      inference('sup-', [status(thm)], ['46', '47'])).
% 9.92/10.11  thf('49', plain,
% 9.92/10.11      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ 
% 9.92/10.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['45', '48'])).
% 9.92/10.11  thf('50', plain,
% 9.92/10.11      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 9.92/10.11         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 9.92/10.11      inference('sup-', [status(thm)], ['36', '39'])).
% 9.92/10.11  thf('51', plain,
% 9.92/10.11      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 9.92/10.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('demod', [status(thm)], ['49', '50'])).
% 9.92/10.11  thf('52', plain,
% 9.92/10.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.92/10.11         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 9.92/10.11          | ~ (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 9.92/10.11          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 9.92/10.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 9.92/10.11          | ~ (l1_pre_topc @ X22)
% 9.92/10.11          | ~ (v2_pre_topc @ X22)
% 9.92/10.11          | (v2_struct_0 @ X22))),
% 9.92/10.11      inference('cnf', [status(esa)], [d1_connsp_2])).
% 9.92/10.11  thf('53', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((v2_struct_0 @ sk_A)
% 9.92/10.11          | ~ (v2_pre_topc @ sk_A)
% 9.92/10.11          | ~ (l1_pre_topc @ sk_A)
% 9.92/10.11          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 9.92/10.11          | ~ (r2_hidden @ X0 @ 
% 9.92/10.11               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('sup-', [status(thm)], ['51', '52'])).
% 9.92/10.11  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('56', plain,
% 9.92/10.11      (![X0 : $i]:
% 9.92/10.11         ((v2_struct_0 @ sk_A)
% 9.92/10.11          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 9.92/10.11          | ~ (r2_hidden @ X0 @ 
% 9.92/10.11               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 9.92/10.11          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.92/10.11      inference('demod', [status(thm)], ['53', '54', '55'])).
% 9.92/10.11  thf('57', plain,
% 9.92/10.11      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 9.92/10.11        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 9.92/10.11        | (v2_struct_0 @ sk_A))),
% 9.92/10.11      inference('sup-', [status(thm)], ['44', '56'])).
% 9.92/10.11  thf('58', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('59', plain,
% 9.92/10.11      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 9.92/10.11        | (v2_struct_0 @ sk_A))),
% 9.92/10.11      inference('demod', [status(thm)], ['57', '58'])).
% 9.92/10.11  thf('60', plain,
% 9.92/10.11      (~ (m1_connsp_2 @ 
% 9.92/10.11          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 9.92/10.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.92/10.11  thf('61', plain,
% 9.92/10.11      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 9.92/10.11         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 9.92/10.11      inference('sup-', [status(thm)], ['36', '39'])).
% 9.92/10.11  thf('62', plain,
% 9.92/10.11      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 9.92/10.11      inference('demod', [status(thm)], ['60', '61'])).
% 9.92/10.11  thf('63', plain, ((v2_struct_0 @ sk_A)),
% 9.92/10.11      inference('clc', [status(thm)], ['59', '62'])).
% 9.92/10.11  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 9.92/10.11  
% 9.92/10.11  % SZS output end Refutation
% 9.92/10.11  
% 9.92/10.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
