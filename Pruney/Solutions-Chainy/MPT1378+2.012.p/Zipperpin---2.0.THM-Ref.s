%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rbYvAYFcQQ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:46 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 144 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  677 (2487 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
        = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X7 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ( m1_connsp_2 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('52',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C_1 @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rbYvAYFcQQ
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 594 iterations in 0.398s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.88  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.67/0.88  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.67/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.88  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.67/0.88  thf(t3_connsp_2, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88               ( ![D:$i]:
% 0.67/0.88                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.67/0.88                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.67/0.88                     ( m1_connsp_2 @
% 0.67/0.88                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88            ( l1_pre_topc @ A ) ) =>
% 0.67/0.88          ( ![B:$i]:
% 0.67/0.88            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.88              ( ![C:$i]:
% 0.67/0.88                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                  ( ![D:$i]:
% 0.67/0.88                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.67/0.88                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.67/0.88                        ( m1_connsp_2 @
% 0.67/0.88                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.67/0.88  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('1', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(d1_connsp_2, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.67/0.88                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.67/0.88          | ~ (m1_connsp_2 @ X21 @ X20 @ X19)
% 0.67/0.88          | (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.67/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.67/0.88          | ~ (l1_pre_topc @ X20)
% 0.67/0.88          | ~ (v2_pre_topc @ X20)
% 0.67/0.88          | (v2_struct_0 @ X20))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.67/0.88  thf('4', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v2_struct_0 @ sk_A)
% 0.67/0.88          | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.67/0.88          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.88  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v2_struct_0 @ sk_A)
% 0.67/0.88          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.67/0.88          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.67/0.88        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['1', '7'])).
% 0.67/0.88  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['8', '9'])).
% 0.67/0.88  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.67/0.88      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('13', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('14', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(dt_k4_subset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.67/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.67/0.88       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.67/0.88          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 0.67/0.88          | (m1_subset_1 @ (k4_subset_1 @ X11 @ X10 @ X12) @ 
% 0.67/0.88             (k1_zfmisc_1 @ X11)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0) @ 
% 0.67/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['13', '16'])).
% 0.67/0.88  thf('18', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(redefinition_k4_subset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.67/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.67/0.88       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.67/0.88          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.67/0.88          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.67/0.88  thf('21', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.67/0.88            = (k2_xboole_0 @ sk_C_1 @ X0))
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 0.67/0.88         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['18', '21'])).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['17', '22'])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t48_tops_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88               ( ( r1_tarski @ B @ C ) =>
% 0.67/0.88                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.67/0.88          | ~ (r1_tarski @ X16 @ X18)
% 0.67/0.88          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ (k1_tops_1 @ X17 @ X18))
% 0.67/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.67/0.88          | ~ (l1_pre_topc @ X17))),
% 0.67/0.88      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ sk_A)
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.67/0.88          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.67/0.88  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.67/0.88          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      ((~ (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))
% 0.67/0.88        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.67/0.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['23', '28'])).
% 0.67/0.88  thf(d3_tarski, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.67/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      (![X1 : $i, X3 : $i]:
% 0.67/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf(d3_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.67/0.88       ( ![D:$i]:
% 0.67/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.88           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X4 @ X7)
% 0.67/0.88          | (r2_hidden @ X4 @ X6)
% 0.67/0.88          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.67/0.88         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X7))),
% 0.67/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88         ((r1_tarski @ X0 @ X1)
% 0.67/0.88          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['30', '32'])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      (![X1 : $i, X3 : $i]:
% 0.67/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf('35', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         ((r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.67/0.88          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['35'])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.67/0.88        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '36'])).
% 0.67/0.88  thf('38', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.67/0.88          | (r2_hidden @ X0 @ X2)
% 0.67/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.88  thf('39', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((r2_hidden @ X0 @ 
% 0.67/0.88           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 0.67/0.88          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.88  thf('40', plain,
% 0.67/0.88      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['12', '39'])).
% 0.67/0.88  thf('41', plain,
% 0.67/0.88      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['17', '22'])).
% 0.67/0.88  thf('42', plain,
% 0.67/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.67/0.88          | ~ (r2_hidden @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.67/0.88          | (m1_connsp_2 @ X21 @ X20 @ X19)
% 0.67/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.67/0.88          | ~ (l1_pre_topc @ X20)
% 0.67/0.88          | ~ (v2_pre_topc @ X20)
% 0.67/0.88          | (v2_struct_0 @ X20))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.67/0.88  thf('43', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v2_struct_0 @ sk_A)
% 0.67/0.88          | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 0.67/0.88          | ~ (r2_hidden @ X0 @ 
% 0.67/0.88               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.88  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('46', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((v2_struct_0 @ sk_A)
% 0.67/0.88          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ X0)
% 0.67/0.88          | ~ (r2_hidden @ X0 @ 
% 0.67/0.88               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 0.67/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.67/0.88  thf('47', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.67/0.88        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['40', '46'])).
% 0.67/0.88  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('49', plain,
% 0.67/0.88      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['47', '48'])).
% 0.67/0.88  thf('50', plain,
% 0.67/0.88      (~ (m1_connsp_2 @ 
% 0.67/0.88          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('51', plain,
% 0.67/0.88      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_D_1)
% 0.67/0.88         = (k2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['18', '21'])).
% 0.67/0.88  thf('52', plain,
% 0.67/0.88      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C_1 @ sk_D_1) @ sk_A @ sk_B)),
% 0.67/0.88      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.88  thf('53', plain, ((v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('clc', [status(thm)], ['49', '52'])).
% 0.67/0.88  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
